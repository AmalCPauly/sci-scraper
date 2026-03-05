import argparse
import csv
import hashlib
import json
import logging
import re
import sqlite3
import time
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Dict, Iterator, List, Optional, Tuple
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse
from urllib.robotparser import RobotFileParser

import requests
from bs4 import BeautifulSoup


DATE_CANDIDATE_FORMATS = [
    "%Y-%m-%d",
    "%Y/%m/%d",
    "%d-%m-%Y",
    "%d/%m/%Y",
    "%d.%m.%Y",
    "%d-%b-%Y",
    "%d-%B-%Y",
    "%d %b %Y",
    "%d %B %Y",
]


@dataclass
class JudgmentRecord:
    source_id: str
    case_title: str
    judgment_date: date
    pdf_url: str
    neutral_citation: Optional[str] = None
    diary_number: Optional[str] = None
    case_number: Optional[str] = None
    petitioner_respondent: Optional[str] = None
    petitioner_respondent_advocate: Optional[str] = None
    judgment_by: Optional[str] = None
    detail_url: Optional[str] = None
    bench: Optional[str] = None
    citation: Optional[str] = None
    reportable_raw: Optional[str] = None


@dataclass
class CaseRef:
    diary_no: str
    diary_year: str
    tab_name: str


class DownloadState:
    def __init__(self, db_path: Path) -> None:
        self.db_path = db_path
        self.conn = sqlite3.connect(self.db_path)
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS downloads (
                source_id TEXT PRIMARY KEY,
                case_title TEXT NOT NULL,
                judgment_date TEXT NOT NULL,
                bench TEXT,
                citation TEXT,
                pdf_url TEXT NOT NULL,
                detail_url TEXT,
                local_path TEXT,
                status TEXT NOT NULL,
                error TEXT,
                updated_at TEXT NOT NULL
            )
            """
        )
        self.conn.commit()

    def is_downloaded(self, source_id: str) -> bool:
        row = self.conn.execute(
            "SELECT status, local_path FROM downloads WHERE source_id = ?", (source_id,)
        ).fetchone()
        if not row:
            return False
        status, local_path = row
        if status != "downloaded":
            return False
        if not local_path:
            return False
        return Path(local_path).exists()

    def mark_downloaded(self, record: JudgmentRecord, local_path: Path) -> None:
        self.conn.execute(
            """
            INSERT INTO downloads (
                source_id, case_title, judgment_date, bench, citation, pdf_url,
                detail_url, local_path, status, error, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(source_id) DO UPDATE SET
                case_title=excluded.case_title,
                judgment_date=excluded.judgment_date,
                bench=excluded.bench,
                citation=excluded.citation,
                pdf_url=excluded.pdf_url,
                detail_url=excluded.detail_url,
                local_path=excluded.local_path,
                status=excluded.status,
                error=excluded.error,
                updated_at=excluded.updated_at
            """,
            (
                record.source_id,
                record.case_title,
                record.judgment_date.isoformat(),
                record.bench,
                record.citation,
                record.pdf_url,
                record.detail_url,
                str(local_path),
                "downloaded",
                None,
                datetime.now().isoformat(timespec="seconds"),
            ),
        )
        self.conn.commit()

    def mark_failed(self, record: JudgmentRecord, error: str) -> None:
        self.conn.execute(
            """
            INSERT INTO downloads (
                source_id, case_title, judgment_date, bench, citation, pdf_url,
                detail_url, local_path, status, error, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(source_id) DO UPDATE SET
                case_title=excluded.case_title,
                judgment_date=excluded.judgment_date,
                bench=excluded.bench,
                citation=excluded.citation,
                pdf_url=excluded.pdf_url,
                detail_url=excluded.detail_url,
                local_path=excluded.local_path,
                status=excluded.status,
                error=excluded.error,
                updated_at=excluded.updated_at
            """,
            (
                record.source_id,
                record.case_title,
                record.judgment_date.isoformat(),
                record.bench,
                record.citation,
                record.pdf_url,
                record.detail_url,
                None,
                "failed",
                error,
                datetime.now().isoformat(timespec="seconds"),
            ),
        )
        self.conn.commit()


class SciJudgmentScraper:
    def __init__(self, args: argparse.Namespace) -> None:
        self.args = args
        self.output_dir = Path(args.output_dir).resolve()
        self.output_dir.mkdir(parents=True, exist_ok=True)

        self.state = DownloadState(self.output_dir / "download_state.sqlite3")
        self.failure_log_path = self.output_dir / "failed_downloads.csv"
        self.metadata_path = self.output_dir / "metadata.csv"

        self.session = requests.Session()
        self.session.headers.update(
            {
                "User-Agent": args.user_agent,
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Accept-Language": args.accept_language,
                "Connection": "keep-alive",
                "Upgrade-Insecure-Requests": "1",
            }
        )
        if args.referer:
            self.session.headers.update({"Referer": args.referer})

        self.robot_parser = RobotFileParser()
        self.robot_parser.set_url(urljoin(args.index_url, "/robots.txt"))
        if args.respect_robots:
            try:
                self.robot_parser.read()
            except Exception as exc:
                logging.warning("Could not read robots.txt: %s", exc)

        self.last_request_at = 0.0
        self._session_bootstrapped = False
        self._init_csv_files()

    def _init_csv_files(self) -> None:
        metadata_header = [
            "neutral_citation",
            "source_id",
            "diary_number",
            "case_number",
            "petitioner_respondent",
            "case_title",
            "petitioner_respondent_advocate",
            "judgment_date",
            "judgment_by",
            "bench",
            "citation",
            "reportable_raw",
            "detail_url",
            "pdf_url",
            "local_path",
        ]
        if self.metadata_path.exists():
            try:
                with self.metadata_path.open("r", newline="", encoding="utf-8") as f:
                    first_row = next(csv.reader(f), [])
                if first_row != metadata_header:
                    rotated = self.metadata_path.with_name(
                        f"metadata_legacy_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
                    )
                    self.metadata_path.replace(rotated)
                    logging.warning("Existing metadata.csv schema changed. Rotated to %s", rotated)
            except Exception:
                pass
        if not self.metadata_path.exists():
            with self.metadata_path.open("w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(metadata_header)

        if not self.failure_log_path.exists():
            with self.failure_log_path.open("w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(["timestamp", "source_id", "pdf_url", "error"])

    def _sleep_if_needed(self) -> None:
        elapsed = time.time() - self.last_request_at
        if elapsed < self.args.min_interval:
            time.sleep(self.args.min_interval - elapsed)

    def _allowed_by_robots(self, url: str) -> bool:
        if not self.args.respect_robots:
            return True
        if self.args.allow_admin_ajax and is_admin_ajax_url(url):
            return True
        try:
            return self.robot_parser.can_fetch(self.args.user_agent, url)
        except Exception:
            return True

    def _request(self, method: str, url: str, **kwargs) -> requests.Response:
        if not self._allowed_by_robots(url):
            raise PermissionError(f"Blocked by robots.txt: {url}")

        if self.args.bootstrap_session and not self._session_bootstrapped:
            self._bootstrap_session()

        attempt = 0
        did_403_recovery = False
        while True:
            attempt += 1
            try:
                self._sleep_if_needed()
                response = self.session.request(method, url, timeout=self.args.timeout, **kwargs)
                self.last_request_at = time.time()

                if response.status_code == 403:
                    if method.upper() == "GET" and self.args.bootstrap_session and not did_403_recovery:
                        logging.warning("403 from %s, retrying once after session bootstrap", url)
                        self._bootstrap_session(force=True)
                        did_403_recovery = True
                        continue
                    raise PermissionError(
                        "403 Forbidden from server. Try passing --api-url (preferred), "
                        "or run with a browser-like --user-agent and valid --referer."
                    )

                if response.status_code in {429, 500, 502, 503, 504}:
                    raise requests.HTTPError(f"Retryable status code: {response.status_code}")

                response.raise_for_status()
                return response
            except Exception:
                if attempt > self.args.retries:
                    raise
                backoff = self.args.min_interval * (2 ** (attempt - 1))
                time.sleep(backoff)

    def _bootstrap_session(self, force: bool = False) -> None:
        if self._session_bootstrapped and not force:
            return
        bootstrap_urls = [self.args.site_home_url, self.args.index_url]
        for target in bootstrap_urls:
            try:
                self._sleep_if_needed()
                response = self.session.get(target, timeout=self.args.timeout, allow_redirects=True)
                self.last_request_at = time.time()
                logging.debug("Bootstrap %s -> %s", target, response.status_code)
            except Exception as exc:
                logging.debug("Bootstrap request failed for %s: %s", target, exc)
        self._session_bootstrapped = True

    def run(self) -> None:
        start_date, end_date = resolve_date_range(self.args)
        logging.info("Target date range: %s to %s", start_date, end_date)

        processed = 0
        downloaded = 0
        skipped = 0
        failed = 0

        for record in self.iter_reportable_records(start_date, end_date):
            if not self.should_keep_by_reportable_mode(record):
                skipped += 1
                continue
            processed += 1
            if self.state.is_downloaded(record.source_id):
                skipped += 1
                continue

            try:
                local_path = self.download_record(record)

                if self.args.reportable_mode == "reportable" and self.args.reportable_check in {
                    "pdf",
                    "metadata_or_pdf",
                }:
                    if not is_pdf_reportable(local_path):
                        skipped += 1
                        try:
                            local_path.unlink(missing_ok=True)
                        except Exception:
                            pass
                        continue

                neutral = extract_neutral_citation_from_pdf(local_path) or record.neutral_citation
                if neutral:
                    record.neutral_citation = neutral
                    local_path = self.rename_with_neutral_citation(local_path, neutral)

                self.state.mark_downloaded(record, local_path)
                self.write_metadata(record, local_path)
                downloaded += 1
            except Exception as exc:
                failed += 1
                self.state.mark_failed(record, str(exc))
                self.write_failure(record, str(exc))
                logging.exception("Failed to download %s", record.source_id)

        logging.info(
            "Done. processed=%s downloaded=%s skipped=%s failed=%s",
            processed,
            downloaded,
            skipped,
            failed,
        )
        if processed == 0:
            logging.warning(
                "No judgment records were discovered for the selected range. "
                "The current listing page may be JS/API-driven or blocked; "
                "run with --log-level DEBUG and prefer --api-url from browser Network tab."
            )

    def should_keep_by_reportable_mode(self, record: JudgmentRecord) -> bool:
        if self.args.reportable_mode == "all":
            return True

        if is_non_reportable_value(record.reportable_raw):
            return False
        if is_reportable_value(record.reportable_raw):
            return True

        if self.args.reportable_check == "metadata":
            return False
        return True

    def iter_reportable_records(self, start_date: date, end_date: date) -> Iterator[JudgmentRecord]:
        if self.args.api_url:
            yield from self._iter_from_api(start_date, end_date)
            return
        if self.args.human_captcha:
            yield from self._iter_from_human_captcha_date_form(start_date, end_date)
            return
        yield from self._iter_from_html(start_date, end_date)

    def _iter_from_api(self, start_date: date, end_date: date) -> Iterator[JudgmentRecord]:
        page = 1
        emitted_ids = set()

        while page <= self.args.max_pages:
            url = build_url_with_query(
                self.args.api_url,
                {
                    self.args.page_param: page,
                    self.args.from_date_param: start_date.isoformat(),
                    self.args.to_date_param: end_date.isoformat(),
                },
            )
            response = self._request("GET", url)
            payload = response.json()

            records = extract_json_records(payload)
            if not records:
                break

            yielded_this_page = 0
            for raw in records:
                record = parse_json_record(raw)
                if not record:
                    continue
                if record.source_id in emitted_ids:
                    continue
                emitted_ids.add(record.source_id)

                if not (start_date <= record.judgment_date <= end_date):
                    continue

                yielded_this_page += 1
                yield record

            if yielded_this_page == 0 and self.args.stop_when_empty_page:
                break
            page += 1

    def _iter_from_html(self, start_date: date, end_date: date) -> Iterator[JudgmentRecord]:
        next_url = self.args.index_url
        visited = set()
        emitted_ids = set()
        page = 0
        captcha_gate_detected = False

        while next_url and page < self.args.max_pages:
            page += 1
            if next_url in visited:
                break
            visited.add(next_url)

            response = self._request("GET", next_url)
            soup = BeautifulSoup(response.text, "html.parser")
            if is_captcha_gated_judgment_page(soup):
                captcha_gate_detected = True

            candidates = parse_html_candidates(soup, next_url)
            for rec in candidates:
                if rec.source_id in emitted_ids:
                    continue
                emitted_ids.add(rec.source_id)

                if not (start_date <= rec.judgment_date <= end_date):
                    continue
                yield rec

            next_url = discover_next_page_url(soup, next_url)

        if captcha_gate_detected:
            logging.warning(
                "Detected CAPTCHA-gated SCI judgments form. Automated record listing from HTML is blocked "
                "without solving CAPTCHA. Use a non-CAPTCHA API source via --api-url, or add a human-in-the-loop captcha step."
            )

    def _iter_from_human_captcha_date_form(self, start_date: date, end_date: date) -> Iterator[JudgmentRecord]:
        if not self.args.captcha_form_url:
            raise ValueError("captcha_form_url is required when --human-captcha is enabled")

        emitted_ids = set()
        for chunk_start, chunk_end in split_date_range(start_date, end_date, self.args.captcha_max_days):
            logging.info("Fetching judgments for %s to %s via CAPTCHA form", chunk_start, chunk_end)
            data, form_fields = self._solve_captcha_and_fetch_first_page(chunk_start, chunk_end)
            if data is None:
                continue

            first_records, pagination, first_case_refs = parse_ajax_payload_to_records(data, self.args.index_url)
            detail_records = self._fetch_records_from_case_refs(first_case_refs)
            combined_first_page = merge_record_lists(first_records, detail_records)
            logging.info(
                "Chunk %s..%s: first page produced %s direct + %s detail records",
                chunk_start,
                chunk_end,
                len(first_records),
                len(detail_records),
            )
            for rec in combined_first_page:
                if rec.source_id in emitted_ids:
                    continue
                emitted_ids.add(rec.source_id)
                if not (start_date <= rec.judgment_date <= end_date):
                    continue
                yield rec

            nonce = pagination.get("nonce")
            page_ids = pagination.get("page_ids", [])
            if not nonce:
                continue

            for page_id in page_ids:
                if page_id <= 1:
                    continue
                page_data = self._fetch_captcha_pagination_page(form_fields, chunk_start, chunk_end, nonce, page_id)
                page_records, _, page_case_refs = parse_ajax_payload_to_records(page_data, self.args.index_url)
                page_detail_records = self._fetch_records_from_case_refs(page_case_refs)
                combined_page = merge_record_lists(page_records, page_detail_records)
                logging.info(
                    "Chunk %s..%s page %s produced %s direct + %s detail records",
                    chunk_start,
                    chunk_end,
                    page_id,
                    len(page_records),
                    len(page_detail_records),
                )
                for rec in combined_page:
                    if rec.source_id in emitted_ids:
                        continue
                    emitted_ids.add(rec.source_id)
                    if not (start_date <= rec.judgment_date <= end_date):
                        continue
                    yield rec

    def _solve_captcha_and_fetch_first_page(
        self, chunk_start: date, chunk_end: date
    ) -> Tuple[Optional[object], Dict[str, str]]:
        if not self.args.human_captcha:
            return None, {}

        captcha_dir = self.output_dir / "captcha"
        captcha_dir.mkdir(parents=True, exist_ok=True)

        for attempt in range(1, self.args.captcha_max_attempts + 1):
            page_response = self._request("GET", self.args.captcha_form_url)
            soup = BeautifulSoup(page_response.text, "html.parser")

            form_fields = extract_captcha_form_hidden_fields(soup)
            if "scid" not in form_fields:
                raise RuntimeError("Could not find required CAPTCHA form fields on SCI page")

            captcha_src = extract_captcha_image_src(soup, self.args.captcha_form_url)
            if not captcha_src:
                raise RuntimeError("Could not find CAPTCHA image on SCI form page")

            captcha_response = self._request("GET", captcha_src, stream=True)
            ext = guess_image_extension(captcha_response.headers.get("Content-Type", ""))
            captcha_path = captcha_dir / f"captcha_{chunk_start.isoformat()}_{chunk_end.isoformat()}_{attempt}.{ext}"
            with captcha_path.open("wb") as f:
                for chunk in captcha_response.iter_content(chunk_size=16384):
                    if chunk:
                        f.write(chunk)

            logging.info("Solve CAPTCHA image: %s", captcha_path)
            if not self.args.interactive_captcha:
                raise RuntimeError(
                    "CAPTCHA requires user input. Run with interactive terminal or enable --interactive-captcha."
                )

            prompt = (
                f"Enter CAPTCHA for {chunk_start.isoformat()}..{chunk_end.isoformat()} "
                "(or 'r' to refresh, 'q' to abort): "
            )
            try:
                entered = input(prompt).strip()
            except EOFError as exc:
                raise RuntimeError("No stdin available for CAPTCHA input") from exc

            if entered.lower() == "q":
                raise KeyboardInterrupt("User aborted during CAPTCHA entry")
            if entered.lower() == "r" or not entered:
                continue

            payload = dict(form_fields)
            payload.update(
                {
                    "from_date": format_indian_date(chunk_start),
                    "to_date": format_indian_date(chunk_end),
                    "siwp_captcha_value": entered,
                    "action": self.args.captcha_action,
                    "language": self.args.language,
                    "es_ajax_request": "1",
                }
            )
            ajax_url = urljoin(self.args.site_home_url, "/wp-admin/admin-ajax.php")
            ajax_response = self._request("GET", ajax_url, params=payload)
            data = ajax_response.json()

            if is_ajax_captcha_error(data):
                logging.warning("CAPTCHA incorrect. Please try again.")
                continue
            if not is_ajax_success(data):
                logging.warning("SCI returned a non-success response for this date chunk: %s", extract_ajax_message(data))
                return None, form_fields
            return data, form_fields

        logging.warning("Exceeded CAPTCHA attempts for %s to %s", chunk_start, chunk_end)
        return None, {}

    def _fetch_captcha_pagination_page(
        self,
        form_fields: Dict[str, str],
        chunk_start: date,
        chunk_end: date,
        nonce: str,
        page_id: int,
    ) -> object:
        payload = dict(form_fields)
        payload.update(
            {
                "from_date": format_indian_date(chunk_start),
                "to_date": format_indian_date(chunk_end),
                "siwp_captcha_value": ".",
                "action": self.args.captcha_action,
                "language": self.args.language,
                "es_ajax_request": "1",
                "sci_pagination_nonce": nonce,
                "sci_page": str(page_id),
            }
        )
        ajax_url = urljoin(self.args.site_home_url, "/wp-admin/admin-ajax.php")
        response = self._request("GET", ajax_url, params=payload)
        data = response.json()
        if not is_ajax_success(data):
            raise RuntimeError(f"Pagination page {page_id} fetch failed")
        return data

    def _fetch_records_from_case_refs(self, case_refs: List[CaseRef]) -> List[JudgmentRecord]:
        if not case_refs:
            return []
        all_records: List[JudgmentRecord] = []
        seen = set()
        for ref in case_refs:
            key = (ref.diary_no, ref.diary_year, ref.tab_name)
            if key in seen:
                continue
            seen.add(key)
            payload = {
                "diary_no": ref.diary_no,
                "diary_year": ref.diary_year,
                "tab_name": ref.tab_name,
                "action": "get_case_details",
                "es_ajax_request": "1",
                "language": self.args.language,
            }
            ajax_url = urljoin(self.args.site_home_url, "/wp-admin/admin-ajax.php")
            response = self._request("GET", ajax_url, params=payload)
            data = response.json()
            if not is_ajax_success(data):
                continue
            detail_html = data.get("data") if isinstance(data, dict) else ""
            if not isinstance(detail_html, str):
                continue
            soup = BeautifulSoup(detail_html, "html.parser")
            all_records.extend(parse_html_candidates(soup, self.args.index_url))
        return all_records

    def download_record(self, record: JudgmentRecord) -> Path:
        target_dir = self.output_dir / str(record.judgment_date.year) / f"{record.judgment_date.month:02d}"
        target_dir.mkdir(parents=True, exist_ok=True)

        case_title_for_file = record.petitioner_respondent or record.case_title
        safe_title = format_case_title_for_filename(case_title_for_file)
        filename = f"{record.judgment_date.strftime('%Y-%m-%d')}-{safe_title}.pdf"
        file_path = dedupe_path(target_dir / filename)

        if self.args.dry_run:
            logging.info("[DRY RUN] %s -> %s", record.pdf_url, file_path)
            return file_path

        response = self._request("GET", record.pdf_url, stream=True)
        content_type = (response.headers.get("Content-Type") or "").lower()
        if "pdf" not in content_type and not record.pdf_url.lower().endswith(".pdf"):
            raise ValueError(f"Not a PDF response: {record.pdf_url} ({content_type})")

        with file_path.open("wb") as f:
            for chunk in response.iter_content(chunk_size=1024 * 64):
                if chunk:
                    f.write(chunk)
        return file_path

    def rename_with_neutral_citation(self, file_path: Path, neutral_citation: str) -> Path:
        neutral_token = normalize_neutral_citation_token(neutral_citation)
        if not neutral_token:
            return file_path
        if file_path.stem.endswith(f"-{neutral_token}"):
            return file_path
        new_name = f"{file_path.stem}-{neutral_token}{file_path.suffix}"
        candidate = dedupe_path(file_path.with_name(new_name))
        file_path.rename(candidate)
        return candidate

    def write_metadata(self, record: JudgmentRecord, local_path: Path) -> None:
        with self.metadata_path.open("a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(
                [
                    record.neutral_citation or "",
                    record.source_id,
                    record.diary_number or "",
                    record.case_number or "",
                    record.petitioner_respondent or record.case_title,
                    record.case_title,
                    record.petitioner_respondent_advocate or "",
                    record.judgment_date.isoformat(),
                    record.judgment_by or "",
                    record.bench or "",
                    record.citation or "",
                    record.reportable_raw or "",
                    record.detail_url or "",
                    record.pdf_url,
                    str(local_path),
                ]
            )

    def write_failure(self, record: JudgmentRecord, error: str) -> None:
        with self.failure_log_path.open("a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(
                [
                    datetime.now().isoformat(timespec="seconds"),
                    record.source_id,
                    record.pdf_url,
                    error,
                ]
            )


def resolve_date_range(args: argparse.Namespace) -> Tuple[date, date]:
    if args.year:
        return date(args.year, 1, 1), date(args.year, 12, 31)
    if args.month:
        dt = datetime.strptime(args.month, "%Y-%m")
        start = date(dt.year, dt.month, 1)
        if dt.month == 12:
            end = date(dt.year, 12, 31)
        else:
            next_month = date(dt.year, dt.month + 1, 1)
            end = next_month.fromordinal(next_month.toordinal() - 1)
        return start, end
    if args.from_date and args.to_date:
        return parse_date(args.from_date), parse_date(args.to_date)
    raise ValueError("Provide either --year, --month, or both --from-date and --to-date")


def parse_date(value: str) -> date:
    value = value.strip()
    for fmt in DATE_CANDIDATE_FORMATS:
        try:
            return datetime.strptime(value, fmt).date()
        except ValueError:
            continue
    raise ValueError(f"Unrecognized date format: {value}")


def sanitize_filename(value: str) -> str:
    cleaned = re.sub(r"[\\/:*?\"<>|]+", "_", value)
    cleaned = re.sub(r"\s+", " ", cleaned).strip().replace(" ", "_")
    return cleaned[:150] or "untitled"


def format_case_title_for_filename(value: str) -> str:
    text = normalize_ws(value)
    text = re.sub(r"\bv\s*/\s*s\b", " vs ", text, flags=re.IGNORECASE)
    text = re.sub(r"\bvs\.?\b", " vs ", text, flags=re.IGNORECASE)
    text = re.sub(r"[^A-Za-z0-9\s]+", " ", text)
    text = normalize_ws(text).title()
    text = re.sub(r"\bVs\b", "vs", text)
    text = text.replace(" ", "_")
    return text[:180] or "Untitled_Case"


def dedupe_path(path: Path) -> Path:
    if not path.exists():
        return path
    stem = path.stem
    suffix = path.suffix
    parent = path.parent
    for i in range(2, 10000):
        candidate = parent / f"{stem}_{i}{suffix}"
        if not candidate.exists():
            return candidate
    raise RuntimeError(f"Could not generate unique file name for {path}")


def is_reportable_value(value: Optional[str]) -> bool:
    if not value:
        return False
    val = value.strip().lower()
    if "non-reportable" in val or "non reportable" in val:
        return False
    return "reportable" in val or val in {"r", "true", "1", "yes"}


def is_non_reportable_value(value: Optional[str]) -> bool:
    if not value:
        return False
    val = value.strip().lower()
    return "non-reportable" in val or "non reportable" in val or val in {"nr", "false", "0", "no"}


def is_pdf_reportable(pdf_path: Path) -> bool:
    try:
        from pypdf import PdfReader
        reader = PdfReader(str(pdf_path))
    except Exception:
        return False
    text_parts: List[str] = []
    for page in reader.pages[:2]:
        try:
            page_text = page.extract_text() or ""
        except Exception:
            page_text = ""
        if page_text:
            text_parts.append(page_text)
    text = " ".join(text_parts)
    text = re.sub(r"\s+", " ", text, flags=re.MULTILINE).strip()
    lower = text.lower()

    # Reject any explicit non-reportable marker, including hyphen/space variants.
    if re.search(r"\bnon\s*[-–]?\s*reportable\b", lower):
        return False
    # Accept only if reportable token exists as a standalone word.
    return bool(re.search(r"\breportable\b", lower))


def extract_neutral_citation_from_pdf(pdf_path: Path) -> Optional[str]:
    try:
        from pypdf import PdfReader

        reader = PdfReader(str(pdf_path))
    except Exception:
        return None

    for page in reader.pages[:2]:
        try:
            page_text = page.extract_text() or ""
        except Exception:
            page_text = ""
        if not page_text:
            continue
        neutral = extract_neutral_citation_from_text(page_text)
        if neutral:
            return neutral
    return None


def extract_neutral_citation_from_text(text: str) -> Optional[str]:
    normalized = re.sub(r"\s+", " ", text).strip()
    m = re.search(r"\b(20\d{2})\s+INSC\s+(\d{1,5})\b", normalized, flags=re.IGNORECASE)
    if not m:
        return None
    return f"{m.group(1)} INSC {m.group(2)}"


def normalize_neutral_citation_token(neutral_citation: str) -> str:
    m = re.search(r"\b(20\d{2})\s+INSC\s+(\d{1,5})\b", neutral_citation, flags=re.IGNORECASE)
    if not m:
        return ""
    return f"{m.group(1)}_INSC_{m.group(2)}"


def build_url_with_query(url: str, params: Dict[str, object]) -> str:
    parsed = urlparse(url)
    current = dict(parse_qsl(parsed.query, keep_blank_values=True))
    for k, v in params.items():
        current[k] = str(v)
    new_query = urlencode(current)
    return urlunparse((parsed.scheme, parsed.netloc, parsed.path, parsed.params, new_query, parsed.fragment))


def extract_json_records(payload: object) -> List[Dict[str, object]]:
    if isinstance(payload, list):
        return [p for p in payload if isinstance(p, dict)]
    if isinstance(payload, dict):
        for key in ["results", "records", "data", "items", "rows"]:
            node = payload.get(key)
            if isinstance(node, list):
                return [p for p in node if isinstance(p, dict)]
    return []


def parse_json_record(raw: Dict[str, object]) -> Optional[JudgmentRecord]:
    case_title = pick_str(raw, ["case_title", "title", "caseName", "name", "subject"])
    judgment_date_raw = pick_str(raw, ["judgment_date", "date", "order_date", "judgementDate"])
    pdf_url = pick_str(raw, ["pdf_url", "pdf", "download_url", "document_url", "url"])
    reportable_raw = pick_str(raw, ["reportable", "reportable_status", "classification", "type"])

    if not case_title or not judgment_date_raw or not pdf_url:
        return None

    try:
        judgment_date = parse_date(judgment_date_raw)
    except ValueError:
        return None

    source_id = pick_str(raw, ["id", "diary_no", "diaryNumber", "uid", "slug"])
    if not source_id:
        key_material = f"{case_title}|{judgment_date.isoformat()}|{pdf_url}"
        source_id = hashlib.sha1(key_material.encode("utf-8")).hexdigest()[:20]

    return JudgmentRecord(
        source_id=str(source_id),
        case_title=case_title,
        judgment_date=judgment_date,
        pdf_url=pdf_url,
        neutral_citation=pick_str(raw, ["neutral_citation", "neutralCitation"]),
        diary_number=pick_str(raw, ["diary_no", "diaryNumber"]),
        case_number=pick_str(raw, ["case_number", "caseNo", "case_no"]),
        petitioner_respondent=pick_str(raw, ["petitioner_respondent", "party_name"]),
        petitioner_respondent_advocate=pick_str(raw, ["petitioner_respondent_advocate", "advocate"]),
        judgment_by=pick_str(raw, ["judgment_by", "judgement_by"]),
        detail_url=pick_str(raw, ["detail_url", "detail", "permalink"]),
        bench=pick_str(raw, ["bench", "coram", "judges"]),
        citation=pick_str(raw, ["citation", "neutral_citation"]),
        reportable_raw=reportable_raw,
    )


def pick_str(data: Dict[str, object], keys: List[str]) -> Optional[str]:
    for key in keys:
        if key in data and data[key] is not None:
            value = str(data[key]).strip()
            if value:
                return value
    return None


def parse_html_candidates(soup: BeautifulSoup, base_url: str) -> List[JudgmentRecord]:
    records: List[JudgmentRecord] = []

    for link in soup.select("a[href]"):
        href = link.get("href")
        if not href:
            continue
        absolute = urljoin(base_url, href)
        link_text = " ".join(link.stripped_strings)
        lowered_url = absolute.lower()
        lowered_text = link_text.lower()
        if not (
            "pdf" in lowered_url
            or "view-pdf" in lowered_url
            or "judgment" in lowered_text
            or "judgement" in lowered_text
            or "download" in lowered_text
            or "pdf" in lowered_text
        ):
            continue

        row = link.find_parent("tr")
        if row is not None:
            row_text = row.get_text(" ", strip=True)
            row_fields = extract_search_row_fields(row)
        else:
            row_text = link.parent.get_text(" ", strip=True) if link.parent else link_text
            row_fields = {}

        maybe_date = extract_first_date(row_text)
        if not maybe_date:
            maybe_date = extract_date_from_pdf_url(absolute)
        if not maybe_date:
            continue

        case_title = row_fields.get("petitioner_respondent") or extract_case_title(row_text)
        source_id = build_source_id_from_html(absolute, case_title, maybe_date)
        reportable_raw = infer_reportable_status(row_text, link_text)

        records.append(
            JudgmentRecord(
                source_id=source_id,
                case_title=case_title,
                judgment_date=maybe_date,
                pdf_url=absolute,
                diary_number=row_fields.get("diary_number"),
                case_number=row_fields.get("case_number"),
                petitioner_respondent=row_fields.get("petitioner_respondent"),
                petitioner_respondent_advocate=row_fields.get("petitioner_respondent_advocate"),
                judgment_by=row_fields.get("judgment_by"),
                detail_url=absolute,
                bench=row_fields.get("bench") or extract_value_after_label(row_text, ["bench", "coram"]),
                citation=extract_value_after_label(row_text, ["citation", "neutral citation"]),
                reportable_raw=reportable_raw,
            )
        )

    return records


def extract_first_date(text: str) -> Optional[date]:
    patterns = [
        r"\b\d{4}-\d{2}-\d{2}\b",
        r"\b\d{4}/\d{2}/\d{2}\b",
        r"\b\d{2}-\d{2}-\d{4}\b",
        r"\b\d{2}/\d{2}/\d{4}\b",
        r"\b\d{2}\.\d{2}\.\d{4}\b",
        r"\b\d{1,2}\s+[A-Za-z]{3,9}\s+\d{4}\b",
    ]
    for pattern in patterns:
        m = re.search(pattern, text)
        if not m:
            continue
        candidate = m.group(0)
        try:
            return parse_date(candidate)
        except ValueError:
            continue
    return None


def extract_date_from_pdf_url(pdf_url: str) -> Optional[date]:
    patterns = [
        r"(\d{2}-[A-Za-z]{3}-\d{4})",
        r"(\d{4}-\d{2}-\d{2})",
        r"(\d{2}-\d{2}-\d{4})",
        r"(\d{2}/\d{2}/\d{4})",
    ]
    for pattern in patterns:
        m = re.search(pattern, pdf_url)
        if not m:
            continue
        token = m.group(1)
        try:
            return parse_date(token)
        except ValueError:
            try:
                return datetime.strptime(token, "%d-%b-%Y").date()
            except ValueError:
                continue
    return None


def extract_search_row_fields(row: BeautifulSoup) -> Dict[str, str]:
    cells = row.find_all("td")
    values = [normalize_ws(c.get_text(" ", strip=True)) for c in cells]
    fields: Dict[str, str] = {}

    if len(values) >= 2:
        fields["diary_number"] = values[1]
    if len(values) >= 3:
        fields["case_number"] = values[2]
    if len(values) >= 4:
        fields["petitioner_respondent"] = values[3]
    if len(values) >= 5:
        fields["petitioner_respondent_advocate"] = values[4]
    if len(values) >= 6:
        fields["bench"] = values[5]
    if len(values) >= 7:
        fields["judgment_by"] = values[6]

    return {k: v for k, v in fields.items() if v}


def infer_reportable_status(row_text: str, link_text: str) -> Optional[str]:
    text = f"{row_text} {link_text}".lower()
    if "non-reportable" in text or "non reportable" in text or re.search(r"\bnr\b", text):
        return "non-reportable"
    if "reportable" in text or re.search(r"\br\b", text):
        return "reportable"
    return None


def extract_case_title(text: str) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    text = re.sub(r"\b(reportable|non-reportable)\b", "", text, flags=re.IGNORECASE).strip()
    date_match = re.search(r"\b\d{1,2}[\-/\s][A-Za-z0-9]{2,9}[\-/\s]\d{4}\b", text)
    if date_match:
        text = text[: date_match.start()].strip(" -|,")
    return text[:200] or "Untitled Case"


def normalize_ws(value: str) -> str:
    return re.sub(r"\s+", " ", value or "").strip()


def build_source_id_from_html(pdf_url: str, case_title: str, judgment_date: date) -> str:
    key = f"{pdf_url}|{case_title}|{judgment_date.isoformat()}"
    return hashlib.sha1(key.encode("utf-8")).hexdigest()[:20]


def extract_value_after_label(text: str, labels: List[str]) -> Optional[str]:
    lower = text.lower()
    for label in labels:
        idx = lower.find(label.lower())
        if idx == -1:
            continue
        seg = text[idx + len(label):]
        seg = seg.lstrip(" :.-")
        seg = seg.split("|", 1)[0].split(";", 1)[0].strip()
        if seg:
            return seg[:200]
    return None


def discover_next_page_url(soup: BeautifulSoup, current_url: str) -> Optional[str]:
    rel_next = soup.find("a", attrs={"rel": lambda x: x and "next" in x})
    if rel_next and rel_next.get("href"):
        return urljoin(current_url, rel_next["href"])

    for anchor in soup.select("a[href]"):
        text = " ".join(anchor.stripped_strings).strip().lower()
        if text in {"next", "next >", ">", "older"} and anchor.get("href"):
            return urljoin(current_url, anchor["href"])
    return None


def split_date_range(start: date, end: date, max_days: int) -> List[Tuple[date, date]]:
    if max_days < 1:
        raise ValueError("max_days must be >= 1")
    chunks: List[Tuple[date, date]] = []
    cursor = start
    while cursor <= end:
        chunk_end = min(end, cursor + timedelta(days=max_days - 1))
        chunks.append((cursor, chunk_end))
        cursor = chunk_end + timedelta(days=1)
    return chunks


def is_admin_ajax_url(url: str) -> bool:
    parsed = urlparse(url)
    return parsed.path.rstrip("/").lower().endswith("/wp-admin/admin-ajax.php")


def format_indian_date(value: date) -> str:
    return value.strftime("%d-%m-%Y")


def extract_captcha_form_hidden_fields(soup: BeautifulSoup) -> Dict[str, str]:
    fields: Dict[str, str] = {}
    form = soup.select_one("form[id^='sciapi-services-judgements-']")
    if form is None:
        return fields

    for tag in form.select("input[name]"):
        name = (tag.get("name") or "").strip()
        if not name:
            continue
        input_type = (tag.get("type") or "text").lower()
        if input_type in {"submit", "reset", "button"}:
            continue
        value = (tag.get("value") or "").strip()
        if input_type == "hidden":
            fields[name] = value
    return fields


def extract_captcha_image_src(soup: BeautifulSoup, page_url: str) -> Optional[str]:
    selectors = [
        "img#siwp_captcha_image_0",
        "img.siwp_img",
        "img#captcha_image",
        "img[src*='_siwp_captcha']",
    ]
    for selector in selectors:
        tag = soup.select_one(selector)
        if tag is None:
            continue
        src = tag.get("src")
        if src:
            return urljoin(page_url, src)

    for tag in soup.find_all("img"):
        src = str(tag.get("src") or "")
        if "_siwp_captcha" in src or "securimage_show.php" in src:
            return urljoin(page_url, src)
    return None


def guess_image_extension(content_type: str) -> str:
    lower = content_type.lower()
    if "png" in lower:
        return "png"
    if "jpeg" in lower or "jpg" in lower:
        return "jpg"
    if "gif" in lower:
        return "gif"
    return "png"


def is_ajax_success(payload: object) -> bool:
    return isinstance(payload, dict) and bool(payload.get("success"))


def is_ajax_captcha_error(payload: object) -> bool:
    if not isinstance(payload, dict):
        return False
    if payload.get("success") is True:
        return False
    data = payload.get("data")
    message = ""
    if isinstance(data, str):
        try:
            parsed = json.loads(data)
            if isinstance(parsed, dict):
                message = str(parsed.get("message") or "")
            else:
                message = data
        except Exception:
            message = data
    elif isinstance(data, dict):
        message = str(data.get("message") or "")
    return "captcha" in message.lower() and ("incorrect" in message.lower() or "required" in message.lower())


def extract_ajax_message(payload: object) -> str:
    if not isinstance(payload, dict):
        return ""
    data = payload.get("data")
    if isinstance(data, str):
        try:
            parsed = json.loads(data)
            if isinstance(parsed, dict):
                return str(parsed.get("message") or data)
        except Exception:
            return data
        return data
    if isinstance(data, dict):
        return str(data.get("message") or "")
    return ""


def parse_ajax_payload_to_records(
    payload: object, base_url: str
) -> Tuple[List[JudgmentRecord], Dict[str, object], List[CaseRef]]:
    if not isinstance(payload, dict):
        return [], {}, []
    if not payload.get("success"):
        return [], {}, []

    data = payload.get("data")
    results_html = ""
    pagination_html = ""
    if isinstance(data, dict):
        results_html = str(data.get("resultsHtml") or data.get("html") or "")
        pagination_html = str(data.get("paginationHtml") or "")
    elif isinstance(data, str):
        results_html = data
    else:
        return [], {}, []

    results_soup = BeautifulSoup(results_html, "html.parser")
    records = parse_html_candidates(results_soup, base_url)
    case_refs = extract_case_refs_from_results_html(results_soup)

    pagination: Dict[str, object] = {"nonce": None, "page_ids": []}
    if pagination_html:
        p_soup = BeautifulSoup(pagination_html, "html.parser")
        pagination_node = p_soup.select_one(".pagination")
        if pagination_node is not None:
            nonce = pagination_node.get("data-nonce")
            if nonce:
                pagination["nonce"] = str(nonce)
        page_ids: List[int] = []
        for anchor in p_soup.select("a[data-page-id]"):
            raw = anchor.get("data-page-id")
            if not raw:
                continue
            try:
                page_ids.append(int(str(raw)))
            except ValueError:
                continue
        if page_ids:
            pagination["page_ids"] = sorted(set(page_ids))
    return records, pagination, case_refs


def extract_case_refs_from_results_html(soup: BeautifulSoup) -> List[CaseRef]:
    refs: List[CaseRef] = []
    for row in soup.select("tr[data-diary-no][data-diary-year][data-tab-name]"):
        diary_no = (row.get("data-diary-no") or "").strip()
        diary_year = (row.get("data-diary-year") or "").strip()
        tab_name = (row.get("data-tab-name") or "").strip()
        if diary_no and diary_year and tab_name:
            refs.append(CaseRef(diary_no=diary_no, diary_year=diary_year, tab_name=tab_name))

    if refs:
        return refs

    for anchor in soup.select(".viewCnrDetails"):
        row = anchor.find_parent("tr")
        if row is None:
            continue
        diary_no = (row.get("data-diary-no") or "").strip()
        diary_year = (row.get("data-diary-year") or "").strip()
        tab_name = (row.get("data-tab-name") or "").strip()
        if diary_no and diary_year and tab_name:
            refs.append(CaseRef(diary_no=diary_no, diary_year=diary_year, tab_name=tab_name))
    return refs


def merge_record_lists(primary: List[JudgmentRecord], secondary: List[JudgmentRecord]) -> List[JudgmentRecord]:
    merged: List[JudgmentRecord] = []
    seen = set()
    for rec in primary + secondary:
        if rec.source_id in seen:
            continue
        seen.add(rec.source_id)
        merged.append(rec)
    return merged


def is_captcha_gated_judgment_page(soup: BeautifulSoup) -> bool:
    if soup.select_one("input[name='siwp_captcha_value']") is not None:
        return True
    if soup.select_one("img.siwp_captcha_image") is not None:
        return True
    if soup.select_one("#captcha_image") is not None:
        return True
    forms = soup.select("form[id^='sciapi-services-judgements-']")
    return bool(forms)


def configure_logging(level: str) -> None:
    numeric = getattr(logging, level.upper(), logging.INFO)
    logging.basicConfig(
        level=numeric,
        format="%(asctime)s | %(levelname)s | %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
    )


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Download reportable Supreme Court judgments as PDFs with metadata, "
            "date filtering, duplicate protection, and download logs."
        )
    )

    date_group = parser.add_argument_group("Date filters (choose one mode)")
    date_group.add_argument("--year", type=int, help="Download all reportable judgments for a year, e.g. 2023")
    date_group.add_argument("--month", help="Download all reportable judgments for a month, e.g. 2023-01")
    date_group.add_argument("--from-date", help="Custom start date, e.g. 2023-01-01")
    date_group.add_argument("--to-date", help="Custom end date, e.g. 2023-01-31")

    parser.add_argument("--index-url", default="https://www.sci.gov.in/judgements/", help="Judgments list URL")
    parser.add_argument("--site-home-url", default="https://www.sci.gov.in/", help="Home page used for cookie/session bootstrap")
    parser.add_argument("--api-url", help="Optional JSON endpoint URL for judgment listing")
    parser.add_argument(
        "--human-captcha",
        action="store_true",
        help="Use SCI judgment-date form with manual CAPTCHA solving (human-in-the-loop).",
    )
    parser.add_argument(
        "--captcha-form-url",
        default="https://www.sci.gov.in/judgements-judgement-date/",
        help="SCI form URL used for manual CAPTCHA mode",
    )
    parser.add_argument(
        "--captcha-action",
        default="get_judgements_judgement_date",
        help="AJAX action name used by SCI form",
    )
    parser.add_argument(
        "--captcha-max-attempts",
        type=int,
        default=10,
        help="Maximum CAPTCHA retries per date chunk",
    )
    parser.add_argument(
        "--captcha-max-days",
        type=int,
        default=30,
        help="Maximum days per query chunk for CAPTCHA mode",
    )
    parser.add_argument(
        "--interactive-captcha",
        action="store_true",
        default=True,
        help="Prompt in terminal for CAPTCHA input",
    )
    parser.add_argument("--no-interactive-captcha", dest="interactive_captcha", action="store_false")
    parser.add_argument("--language", default="en", help="Language param for SCI AJAX requests")

    parser.add_argument("--output-dir", default="downloads", help="Root output folder")
    parser.add_argument("--dry-run", action="store_true", help="Discover and log without downloading PDFs")
    parser.add_argument(
        "--reportable-mode",
        default="reportable",
        choices=["reportable", "all"],
        help="Download only reportable records (default) or all records.",
    )
    parser.add_argument(
        "--reportable-check",
        default="pdf",
        choices=["metadata", "metadata_or_pdf", "pdf"],
        help=(
            "How to classify reportable records when --reportable-mode=reportable: "
            "metadata only, metadata fallback to PDF text, or PDF text only."
        ),
    )

    parser.add_argument("--min-interval", type=float, default=1.5, help="Minimum seconds between HTTP requests")
    parser.add_argument("--timeout", type=float, default=30.0, help="HTTP timeout in seconds")
    parser.add_argument("--retries", type=int, default=3, help="Retries on transient failures")
    parser.add_argument("--max-pages", type=int, default=500, help="Hard stop for pagination")
    parser.add_argument("--respect-robots", action="store_true", default=True, help="Honor robots.txt")
    parser.add_argument("--no-respect-robots", dest="respect_robots", action="store_false")
    parser.add_argument(
        "--allow-admin-ajax",
        action="store_true",
        help="Allow SCI /wp-admin/admin-ajax.php requests even when robots checks are enabled (required for human-captcha mode).",
    )
    parser.add_argument(
        "--bootstrap-session",
        action="store_true",
        default=True,
        help="Warm up session cookies before scraping pages",
    )
    parser.add_argument("--no-bootstrap-session", dest="bootstrap_session", action="store_false")
    parser.add_argument(
        "--user-agent",
        default=(
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/132.0.0.0 Safari/537.36"
        ),
        help="User agent for HTTP requests",
    )
    parser.add_argument("--referer", default="https://www.sci.gov.in/", help="Referer header")
    parser.add_argument("--accept-language", default="en-IN,en;q=0.9", help="Accept-Language header")

    parser.add_argument("--page-param", default="page", help="Pagination query param for API mode")
    parser.add_argument("--from-date-param", default="from_date", help="Start-date query param for API mode")
    parser.add_argument("--to-date-param", default="to_date", help="End-date query param for API mode")
    parser.add_argument(
        "--stop-when-empty-page",
        action="store_true",
        default=True,
        help="In API mode, stop when a page yields no usable records",
    )
    parser.add_argument("--log-level", default="INFO", choices=["DEBUG", "INFO", "WARNING", "ERROR"])

    return parser


def main() -> int:
    parser = build_arg_parser()
    args = parser.parse_args()
    configure_logging(args.log_level)

    try:
        scraper = SciJudgmentScraper(args)
        if args.human_captcha and args.respect_robots and not args.allow_admin_ajax:
            logging.warning(
                "Human CAPTCHA mode requires SCI admin-ajax endpoint; with strict robots mode this may fail. "
                "If permitted for your project, add --allow-admin-ajax."
            )
        scraper.run()
        return 0
    except Exception as exc:
        logging.exception("Fatal error: %s", exc)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

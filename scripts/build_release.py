#!/usr/bin/env python3
"""
Build a clean release zip and MANIFEST.md for the path-compression-digestion folder.
"""

from __future__ import annotations

import hashlib
import subprocess
import sys
import zipfile
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RELEASE = ROOT / "release"

LATEX_BUILD_SUFFIXES = {
    ".aux",
    ".bbl",
    ".blg",
    ".log",
    ".out",
    ".toc",
    ".fdb_latexmk",
    ".fls",
    ".synctex.gz",
}

EXPECTED = [
    "README.md",
    "AGENTS.md",
    "CURRENT_STATUS.md",
    "CHANGELOG.md",
    "proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md",
    "publication/abstract/path_compression_v2_1_abstract.md",
    "publication/talk_outline/path_compression_v2_1_talk_outline.md",
    "audits/path_compression_v2_integrated_proof_note_AUDIT.md",
    "audits/path_compression_v2_2_self_audit.md",
    "audits/path_compression_v2_2_publication_packaging_VERIFICATION.md",
    "manifests/path_compression_v2_2_publication_packet_manifest.md",
    "scripts/sanity_check_j_thresholds.py",
]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def check_expected() -> None:
    missing = [p for p in EXPECTED if not (ROOT / p).exists()]
    if missing:
        print("Missing expected files:", file=sys.stderr)
        for p in missing:
            print(f"  - {p}", file=sys.stderr)
        raise SystemExit(1)


def run_sanity() -> None:
    script = ROOT / "scripts" / "sanity_check_j_thresholds.py"
    subprocess.run([sys.executable, str(script)], cwd=ROOT, check=True)


def is_latex_build_artifact(rel: Path) -> bool:
    return any(rel.as_posix().endswith(suffix) for suffix in LATEX_BUILD_SUFFIXES)


def all_release_files() -> list[Path]:
    skip_dirs = {".git", "__pycache__"}
    files = []
    for path in ROOT.rglob("*"):
        rel = path.relative_to(ROOT)
        if any(part in skip_dirs for part in rel.parts):
            continue
        if rel.parts[0] == "release" and path.suffix == ".zip":
            continue
        # Exclude generated LaTeX intermediates; paper/main.pdf is intentionally
        # included as the compiled paper artifact alongside its source files.
        if is_latex_build_artifact(rel):
            continue
        if path.is_file():
            files.append(path)
    return sorted(files, key=lambda p: str(p.relative_to(ROOT)))


def write_manifest(files: list[Path]) -> None:
    lines = [
        "# Clean Folder Manifest",
        "",
        f"Generated: {datetime.now(timezone.utc).isoformat()}",
        "",
        "| file | SHA-256 |",
        "|---|---|",
    ]
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        if rel == "MANIFEST.md":
            continue
        lines.append(f"| `{rel}` | `{sha256(path)}` |")
    (ROOT / "MANIFEST.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_zip(files: list[Path]) -> Path:
    RELEASE.mkdir(exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = RELEASE / f"path-compression-digestion-clean-{stamp}.zip"
    with zipfile.ZipFile(out, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for path in files:
            rel = path.relative_to(ROOT)
            z.write(path, Path("path-compression-digestion") / rel)
    return out


def main() -> None:
    check_expected()
    run_sanity()
    files = all_release_files()
    write_manifest(files)
    files = all_release_files()
    out = build_zip(files)
    print(f"ok: built {out}")


if __name__ == "__main__":
    main()

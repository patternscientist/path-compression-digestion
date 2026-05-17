# Codex Prompt: Release Builder

Read `AGENTS.md`.

Task:
Inspect `scripts/build_release.py` and improve it if necessary.

The release builder should:

1. verify expected files exist;
2. compute SHA-256 hashes;
3. run `scripts/sanity_check_j_thresholds.py`;
4. build a timestamped zip in `release/`;
5. write or update `MANIFEST.md`;
6. fail loudly if critical files are missing.

Do not change the proof note unless the script exposes a concrete stale-reference bug.

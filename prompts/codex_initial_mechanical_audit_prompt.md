# Codex Prompt: Initial Mechanical Packet Audit

Read `AGENTS.md`, `README.md`, and `CURRENT_STATUS.md`.

You are acting as a mechanical publication-packet auditor, not as a proof author.

Do not rewrite the proof architecture.
Do not change theorem statements unless there is an explicit logical bug.
Do not invent new mathematics.
Do not broaden into a literature review.

Task:
Audit this clean path-compression publication workspace mechanically and produce minimal repairs only.

Required checks:

1. List all files in the workspace.
2. Compare `manifests/path_compression_v2_2_publication_packet_manifest.md` against actual files.
3. Check for stale or inconsistent filenames, especially references to:
   - `latest-correct.zip`
   - `path_compression_v2_1_publication_packet_COMPLETE.zip`
   - `latest-latest(1).zip`
   - any old v1/v2/v2.1 name used as if it were current.
4. Search for the phrase `Equivalently` near Theorem 4.7. If it states only
   `A(z,4Q)>r => J_{z+1}(r)<=Q`
   as equivalent to
   `R_{z+1}(Q)>=A(z,4Q)`,
   patch it to `Consequently` unless a genuinely equivalent integer statement is written.
5. Check that `alpha_Q` existence is justified.
6. Check that Lemma 4.3 explicitly declares `B,t` as nonnegative integers.
7. Check consistency of:
   - `Q(m,n)=ceil(1+m/n)`
   - `L(n)=ceil(log_2 max(n,2))`
   - theorem target `R_{z+1}(Q)>=A(z,4Q)`.
8. Check whether all source/provenance files mentioned in the manifest are present somewhere in this workspace. If not, do not fabricate them; patch `MANIFEST.md` or write a clear missing-file note.
9. Run `python scripts/sanity_check_j_thresholds.py` and report the output.
10. If useful, run `python scripts/build_release.py` to create a release zip.

Return:
- concise audit report;
- exact files changed;
- unified diff summary;
- final `ACCEPT` / `NEEDS_REPAIR` verdict.

Use minimal diffs.

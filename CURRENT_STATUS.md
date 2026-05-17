# Current Status

Verdict before clean-folder assembly: **publication-facing candidate; use Codex for mechanical audit and packaging, not open-ended proof discovery.**

## Mathematical status

The current proof note claims and packages the direct comparison

```text
R_{z+1}(Q) >= A(z,4Q)
```

for the packet Ackermann normalization, implying the desired bridge from the Seidel--Sharir `J` hierarchy to the packet-normalized inverse-Ackermann bound.

The latest surgical repair pass claims to have fixed:

1. the Theorem 4.7 "Equivalently" wording issue;
2. the existence justification for `alpha_Q`;
3. Lemma 4.3's missing nonnegative-integer hypotheses for `B,t`;
4. manifest/provenance separation;
5. verification report naming/content issues.

## What Codex should do next

Codex should first run a mechanical packet audit:

- verify file references;
- check stale filenames;
- check theorem target consistency;
- check whether the latest manifest matches this clean folder;
- run finite sanity checks;
- build a release zip;
- report only minimal diffs.

## What Codex should not do yet

- Do not search for a better proof.
- Do not rewrite the proof note stylistically.
- Do not change definitions or theorem statements.
- Do not broaden the project into a union-find literature review.

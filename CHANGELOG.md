# Changelog: v2.1 to v2.2

This patch does not rewrite the proof body, change theorem statements, or reopen proof search.

## Changes

1. In Theorem 4.7, replaced “Equivalently” with “Consequently,” for the one-way implication
   \[
   A(z,4Q)>r \Longrightarrow J_{z+1}(r)\le Q.
   \]
   The main theorem statement \(R_{z+1}(Q)\ge A(z,4Q)\) is unchanged.

2. Added a short existence justification for \(\alpha_Q(m,n)\) after its definition in Section 5.1.

3. Added the hypothesis that \(B,t\) are nonnegative integers to Lemma 4.3.

4. Updated the publication manifest to distinguish files included in the v2.2 publication-facing packet from external provenance dependencies.

5. Updated the verification report to name the actual final source-anchor packet zip:
   `path_compression_source_anchor_patch_packet.zip`,
   and to include the verification report itself in the expected v2.2 contents list.

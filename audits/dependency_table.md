# Dependency Table

Source file: `proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md`

This table records proof dependencies only. It does not modify the proof note, and it does not treat the finite sanity-check script as a proof dependency.

| label | statement summary | depends on | used by | status |
|---|---|---|---|---|
| S1 source anchors | Seidel--Sharir paper supplies the rank bound, `g^*`, `g^diamond`, shifting lemma, `J_k` hierarchy, source recurrence, and source inverse threshold. | source-anchor packet | S2, S3, S4, S5, S6 | source |
| S2 `g^diamond` definition | For integer `g`, `g^diamond(r)=g(r)` if `g(r)<=1`, otherwise `1+g^diamond(ceil(log_2 g(r)))`. | S1 | J1, R1 | source |
| S3 shifting lemma | If `f(m,n,r) <= k m + 2 n g(r)`, then `f(m,n,r) <= (k+1)m + 2 n g^diamond(r)`. | S1, S2 | S5 | source |
| S4 `J` hierarchy | `J_0(r)=ceil((r-1)/2)` and `J_{k+1}=J_k^diamond`. | S1, S2 | J1, J2, R0, R1 | source |
| S5 source recurrence | The source consequence used for cost is `f(m,n,r) <= k m + 2 n J_k(r)`. | S1, S3, S4 | C1 | source |
| S6 source inverse threshold | Source threshold is `J_k(ceil(log_2 n)) <= 1 + m/n`; packet uses `L(n)` and `Q(m,n)` as normalized thresholds. | S1 | N1, N2, AQ3 | source |
| N1 rank cutoff normalization | `L(n)=ceil(log_2 max(n,2))`; agrees with the source cutoff for `n>=2` and stabilizes `n=1`. | S6 | AQ1, AQ2, AQ3, C1 | derived |
| N2 integer threshold normalization | `Q(m,n)=ceil(1+m/n)` gives an integer threshold for the `R_k` comparison. | S6 | AQ1, AQ2, AQ3, C1 | derived |
| A1 Ackermann normalization | Packet Ackermann function is `A(0,x)=2x`, `A(i,0)=0`, `A(i,1)=2`, and `A(i,x)=A(i-1,A(i,x-1))`. | packet convention | A2, A3, T1, AQ0, AQ1, B1 | explanatory |
| Rdef threshold inverse | `R_k(t)=max { r>=0 : J_k(r)<=t }`; finiteness is justified by the later `J_k` package. | S4, J2 | R0, R1, R2, A3, T1 | derived |
| J1 Lemma 4.1 diamond preservation | `g^diamond` preserves integer-valuedness, nonnegativity, monotonicity, unboundedness, `h(0)=0`, and `h(r)<r` for `r>1`. | S2 | J2 | proved |
| J2 Lemma 4.2 basic `J_k` package | Each `J_k` is integer-valued, nonnegative, nondecreasing, unbounded, has `J_k(0)=0`, satisfies `J_k(r)<r`, and gives finite monotone `R_k` with `R_{k+1}(t)>=R_k(t)`. | S4, J1 | Rdef, R1, R2, A3, T1 | proved |
| R0 exact base inverse | `R_0(t)=2t+1`. | S4, Rdef | R2, A3, T1 | proved |
| R1 Lemma 4.3 threshold recurrence | If `r<=R_k(2^B)` and `B<=R_{k+1}(t)`, then `J_{k+1}(r)<=t+1`; consequently `R_{k+1}(t+1)>=R_k(2^{R_{k+1}(t)})`. | S2, S4, J2, Rdef | R2, A3, T1 | proved |
| R2 Lemma 4.4 threshold jump | For `k>=0` and `Q>=2`, `R_{k+1}(Q)>=R_k(4Q)`. | R1, J2, R0 | T1 | proved |
| A2 Lemma 4.5 Ackermann monotonicity | Ackermann rows are nondecreasing; for `i>=1`, `A(i,x)>=2x`; and row domination gives `A(i+1,x)>=A(i,x)`. | A1 | A3, T1, AQ0, B1 | proved |
| A3 Lemma 4.6 threshold/Ackermann domination | For `j>=1` and `x>=1`, `R_j(x)>=A(j+1,x)`. | R1, R0, J2, A1, A2 | T1 | proved |
| T1 Theorem 4.7 main comparison | For `z>=1` and `Q>=1`, `R_{z+1}(Q)>=A(z,4Q)`; hence `A(z,4Q)>r` implies `J_{z+1}(r)<=Q`. | R1, R2, J2, A2, A3 | AQ1, AQ3 | proved |
| AQ0 alpha definitions and existence | Defines `alpha_J^Q` and `alpha_Q`; proves the minimum for `alpha_Q` exists. | A1, A2, N1, N2 | AQ1, AQ3, C1 | proved |
| AQ1 Theorem 5.1 packet threshold comparison | For positive `m,n`, `alpha_J^Q(m,n) <= alpha_Q(m,n)+1`. | AQ0, T1, N1, N2 | C1, appendix comparison | proved |
| B1 Lemma 5.2 Ackermann buffer | For `z>=1` and integer `p>=1`, `A(z+1,4p)>=A(z,4p+4)`. | A1, A2 | AQ3 | proved |
| AQ2 source-faithful real threshold definition | Defines `alpha_J^S(m,n)=min{k>=0:J_k(L(n))<=1+m/n}`. | S6, N1 | AQ3, appendix source-alpha comparison | derived |
| AQ3 Theorem 5.3 real-threshold comparison | For positive `m,n`, `alpha_J^S(m,n)<=alpha_Q(m,n)+2`; if `1+m/n` is integral, the bound is `+1`. | AQ0, AQ2, T1, B1, N1, N2 | appendix source-alpha comparison | proved |
| C1 Theorem 5.4 cost consequence | Using `f(m,n,r)<=k m + 2n J_k(r)`, obtains `f(m,n,L(n)) <= (alpha_Q(m,n)+3)m + 4n`, hence `O(m alpha_Q(m,n)+n)`. | S5, AQ0, AQ1, N1, N2 | final theorem block | proved |
| APP1 normalization appendix | Explains `alpha_A`, the relationship to `alpha_Q`, comparisons with `alpha_J^Q` and `alpha_J^S`, and the packet relation to source `alpha_S`. | AQ1, AQ3, S6, N1, N2 | reader orientation | explanatory |
| APP2 Tarjan-style convention note | Notes that the source's discussion of Tarjan-style `alpha_T` is not used as a theorem dependency. | S1 | hazards avoided | explanatory |
| H1 hazards avoided | Records avoided normalization hazards: `1+m/n` versus `2m/n`, the `2n` factor, integer `Q`, and avoiding bottom-up Tarjan-potential drift. | S3, S5, S6, N1, N2, T1 | audit/review | explanatory |
| F1 final theorem block | Restates the packet theorem spine, constants `c=1`, `C=1`, `D=4`, alpha comparisons, and cost consequence for citation. | T1, AQ1, AQ3, C1 | publication-facing citation | derived |


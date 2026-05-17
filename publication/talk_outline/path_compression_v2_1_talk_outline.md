# Talk outline: top-down `J` hierarchy and the packet-normalized inverse-Ackermann bound

## 1. Public problem

- Goal: explain, directly from the Seidel--Sharir top-down path-compression recurrence, why the resulting bound is inverse-Ackermann.
- This is not a new union-find asymptotic bound.
- It is a source-anchored proof-digestion answer to the comparison problem: how does the top-down \(J\) hierarchy line up with a classical Ackermann normalization?

## 2. Seidel--Sharir `J` hierarchy

- Source recurrence uses \(g^\diamond\):
  \[
  g^\diamond(r)=g(r)\quad(g(r)\le1),\qquad
  g^\diamond(r)=1+g^\diamond(\lceil\log_2 g(r)\rceil)\quad(g(r)>1).
  \]
- Define
  \[
  J_0(r)=\left\lceil\frac{r-1}{2}\right\rceil,\qquad J_{k+1}=J_k^\diamond.
  \]
- Source recurrence:
  \[
  f(m,n,r)\le km+2nJ_k(r).
  \]

## 3. Threshold inverse \(R_k\)

- Define
  \[
  R_k(t)=\max\{r\ge0:J_k(r)\le t\}.
  \]
- Basic \(J\)-lemmas: \(J_k\) is monotone, unbounded, and \(J_k(r)<r\) for \(r>1\).
- Therefore \(R_k(t)\) is finite for finite \(t\).

## 4. Diamond-to-threshold recurrence

- Key observation: if \(J_k(r)\le 2^B\), then
  \[
  \lceil\log_2 J_k(r)\rceil\le B.
  \]
- Thus, if \(B\le R_{k+1}(t)\),
  \[
  J_{k+1}(r)\le t+1.
  \]
- Threshold recurrence:
  \[
  R_{k+1}(t+1)\ge R_k(2^{R_{k+1}(t)}).
  \]

## 5. Ackermann domination

- Exact base:
  \[
  R_0(t)=2t+1.
  \]
- Main invariant:
  \[
  R_j(x)\ge A(j+1,x)\qquad(j\ge1,\ x\ge1).
  \]
- Main comparison:
  \[
  R_{z+1}(Q)\ge A(z,4Q).
  \]
- Constants:
  \[
  c=1,\qquad C=1,\qquad D=4.
  \]

## 6. Alpha/cost consequence

- Packet threshold:
  \[
  Q(m,n)=\left\lceil1+\frac mn\right\rceil.
  \]
- Packet inverse:
  \[
  \alpha_Q(m,n)=\min\{z\ge1:A(z,4Q(m,n))>L(n)\}.
  \]
- Consequences:
  \[
  \alpha_J^Q(m,n)\le\alpha_Q(m,n)+1,
  \]
  and
  \[
  \alpha_J^S(m,n)\le\alpha_Q(m,n)+2.
  \]
- Cost bound:
  \[
  f(m,n,L(n))\le(\alpha_Q(m,n)+3)m+4n.
  \]

## 7. Hazards avoided

- Do not replace the source threshold \(1+m/n\) by \(2m/n\).
- Keep the factor \(2n\) in the shifting lemma.
- Use \(Q(m,n)=\lceil1+m/n\rceil\) to make the threshold integer-valued.
- Avoid bottom-up Tarjan-potential drift; the proof stays inside the top-down \(J\)-hierarchy.

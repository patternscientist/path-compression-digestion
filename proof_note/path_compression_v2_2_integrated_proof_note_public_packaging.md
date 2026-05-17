# Path compression v2 proof note: top-down `J` hierarchy and the packet-normalized inverse-Ackermann bound

## 1. Executive summary

This note gives a polished, source-faithful v2 packaging of the proof that the Seidel--Sharir top-down `J` hierarchy implies the packet-normalized inverse-Ackermann bound.

The threshold inverse is

\[
R_k(t)=\max\{r\ge 0:J_k(r)\le t\}.
\]

The main comparison theorem is

\[
R_{z+1}(Q)\ge A(z,4Q)
\qquad
(z\ge 1,\ Q\ge 1).
\]

Thus the coordinator comparison target

\[
R_{cz+C}(Q)\ge A(z,DQ)
\]

holds with

\[
c=1,\qquad C=1,\qquad D=4.
\]

For

\[
L(n)=\lceil \log_2\max(n,2)\rceil,
\qquad
Q(m,n)=\left\lceil 1+\frac mn\right\rceil,
\]

and

\[
\alpha_Q(m,n)=\min\{z\ge 1:A(z,4Q(m,n))>L(n)\},
\]

the patched threshold consequence is

\[
\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1,
\]

where

\[
\alpha_J^Q(m,n)=\min\{k\ge 0:J_k(L(n))\le Q(m,n)\}.
\]

For the source-faithful real threshold

\[
J_k(L(n))\le 1+\frac mn,
\]

define

\[
\alpha_J^S(m,n)
=
\min\left\{k\ge0:J_k(L(n))\le 1+\frac mn\right\}.
\]

Then

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+2,
\]

with the sharper bound

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+1
\]

when \(1+m/n\) is integral.

Using the source recurrence

\[
f(m,n,r)\le km+2nJ_k(r),
\]

the cost consequence is

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n
=
O(m\alpha_Q(m,n)+n).
\]

This v2 note integrates the accepted source-fidelity erratum: the shifting lemma uses the source-correct hypothesis \(f(m,n,r)\le km+2ng(r)\), not the earlier shorthand \(km+ng(r)\).

---

## 2. Source-fidelity and packet conventions

This section records exactly which source facts and packet normalizations are used. It does not reprove the Seidel--Sharir path-compression recurrence.

### 2.1 Technical source anchors

The recovered standalone `source_anchors.md` identifies the technical source as:

```text
Raimund Seidel and Micha Sharir,
Top-Down Analysis of Path Compression,
SIAM Journal on Computing 34(3):515--525, 2005.
DOI: 10.1137/S0097539703439088
Author PDF: https://www.math.tau.ac.il/~michas/ufind.pdf
```

The relevant recovered source anchors are:

| item | recovered anchor |
|---|---|
| rank bound | source page 7: a rank-\(k\) root has subtree size at least \(2^k\), so maximum rank is at most \(\log_2 n\) |
| \(g^*\), \(g^\diamond\) | source page 7 |
| shifting lemma | source pages 7--8 |
| \(J_k\) hierarchy and recurrence | source page 9, Corollary 6 |
| source inverse threshold | source page 9, definition of \(\alpha_S\) |
| relation to Tarjan's \(\alpha_T\) | source page 10; this is a comparison discussion, not used as a proof dependency here |

### 2.2 The functions \(g^*\) and \(g^\diamond\)

For an integer-valued \(g\) with \(g(r)<r\) for \(r>0\), the source defines

\[
g^*(r)=
\begin{cases}
0,&r\le 1,\\
1+g^*(g(r)),&r>1,
\end{cases}
\]

and

\[
g^\diamond(r)=
\begin{cases}
g(r),&g(r)\le 1,\\[4pt]
1+g^\diamond(\lceil\log_2 g(r)\rceil),&g(r)>1.
\end{cases}
\]

All logarithms in this note are base \(2\).

### 2.3 Source-correct shifting lemma

The source-correct top-down shifting lemma is:

\[
\boxed{
\text{If } f(m,n,r)\le km+2ng(r),\text{ then }
f(m,n,r)\le (k+1)m+2n g^\diamond(r).
}
\]

This corrects the earlier shorthand \(km+ng(r)\) that appeared in the accepted proof note's source-fidelity block. The mismatch was only a source-fidelity wording issue. The recurrence actually used in the proof,

\[
f(m,n,r)\le km+2nJ_k(r),
\]

is source-anchored and unchanged.

### 2.4 The \(J\) hierarchy and recurrence consequence

The source hierarchy is

\[
J_0(r)=\left\lceil\frac{r-1}{2}\right\rceil,
\qquad
J_{k+1}=J_k^\diamond.
\]

Equivalently,

\[
J_{k+1}(r)=
\begin{cases}
J_k(r),&J_k(r)\le 1,\\[4pt]
1+J_{k+1}(\lceil\log_2 J_k(r)\rceil),&J_k(r)>1.
\end{cases}
\]

The source recurrence consequence is

\[
f(m,n,r)\le km+2nJ_k(r).
\]

This is the only path-compression recurrence used in the final cost bound.

### 2.5 Rank and threshold normalizations

The source rank cutoff is \(\lceil\log_2 n\rceil\). The packet uses the stabilized cutoff

\[
L(n)=\lceil\log_2\max(n,2)\rceil.
\]

For \(n\ge2\), this equals \(\lceil\log_2 n\rceil\); for \(n=1\), it avoids the degenerate cutoff \(0\).

The source inverse threshold is

\[
J_k(\lceil\log_2 n\rceil)\le 1+\frac mn.
\]

The packet integer threshold is

\[
Q(m,n)=\left\lceil 1+\frac mn\right\rceil.
\]

The packet threshold is not a new source theorem; it is a normalization device that converts the real threshold \(1+m/n\) into an integer threshold for the \(R_k\) comparison.

---

## 3. One-page blackboard proof idea

The proof has one moving part: the `diamond` recurrence turns a bound at level \(k\) into a dramatically larger threshold inverse at level \(k+1\).

Define

\[
R_k(t)=\max\{r:J_k(r)\le t\}.
\]

If \(r\le R_k(2^B)\), then \(J_k(r)\le 2^B\). In the recursive branch of \(J_{k+1}=J_k^\diamond\),

\[
J_{k+1}(r)
=
1+J_{k+1}(\lceil\log_2 J_k(r)\rceil),
\]

and the logarithmic argument is at most \(B\). Therefore, if \(B\le R_{k+1}(t)\), then the recursive call costs at most \(t\), and

\[
J_{k+1}(r)\le t+1.
\]

This gives the threshold recurrence

\[
R_{k+1}(t+1)\ge R_k(2^{R_{k+1}(t)}).
\]

That recurrence has Ackermann flavor: increasing the \(J\)-level by one lets us feed an exponential of a previous threshold into the lower-level inverse.

The rest of the proof turns this into a clean invariant:

\[
R_j(x)\ge A(j+1,x)
\qquad
(j\ge1,\ x\ge1).
\]

The base level \(R_0(t)=2t+1\) is too small to dominate \(A(1,t)=2^t\); this is why the comparison has a one-level shift. After proving the invariant, a short threshold jump gives

\[
R_{z+1}(Q)\ge A(z,4Q),
\]

with constants \(c=1,C=1,D=4\).

Finally, the comparison theorem is translated back to the source recurrence. If

\[
A(z,4Q(m,n))>L(n),
\]

then

\[
J_{z+1}(L(n))\le Q(m,n).
\]

Thus \(k=z+1\) suffices in

\[
f(m,n,L(n))\le km+2nJ_k(L(n)),
\]

and the ceiling estimate \(Q(m,n)\le 2+m/n\) gives

\[
f(m,n,L(n))\le(\alpha_Q(m,n)+3)m+4n.
\]

---

## 4. Technical comparison proof

### 4.1 Ackermann normalization

The packet Ackermann function is

\[
A(0,x)=2x,
\]

and for \(i\ge1\),

\[
A(i,0)=0,
\qquad
A(i,1)=2,
\qquad
A(i,x)=A(i-1,A(i,x-1))\quad(x\ge2).
\]

In particular,

\[
A(1,x)=2^x
\]

for \(x\ge1\).

### 4.2 Threshold inverse

For \(t\ge0\), define

\[
R_k(t)=\max\{r\ge0:J_k(r)\le t\}.
\]

The maximum is finite because Lemma 4.2 below proves that each fixed \(J_k\) is unbounded on \(\mathbb N\).

### 4.3 Basic \(J\)-lemma package

#### Lemma 4.1: diamond preservation

Let \(g:\mathbb N\to\mathbb N\) be integer-valued, nonnegative, nondecreasing, unbounded, and satisfy

\[
g(0)=0,
\qquad
g(r)<r\quad(r>1).
\]

Define \(h=g^\diamond\) by

\[
h(r)=
\begin{cases}
g(r),&g(r)\le1,\\[4pt]
1+h(\lceil\log_2 g(r)\rceil),&g(r)>1.
\end{cases}
\]

Then \(h\) is integer-valued, nonnegative, nondecreasing, unbounded, satisfies \(h(0)=0\), and satisfies

\[
h(r)\le g(r)
\quad(r\ge0),
\]

hence

\[
h(r)<r
\quad(r>1).
\]

#### Proof

First note that for every integer \(x\ge2\),

\[
\lceil\log_2 x\rceil\le x-1.
\]

Thus in the recursive branch \(g(r)>1\), with

\[
u=\lceil\log_2 g(r)\rceil,
\]

we have

\[
u\le g(r)-1<r.
\]

So \(h(r)\) is defined by recursion on smaller arguments. It is integer-valued and nonnegative because \(g\) is.

We prove \(h(r)\le g(r)\) by induction on \(r\). If \(g(r)\le1\), then \(h(r)=g(r)\). If \(g(r)>1\), set \(u=\lceil\log_2 g(r)\rceil\). Since \(u<r\), the induction hypothesis gives \(h(u)\le g(u)\). Since \(g(u)<u\) when \(u>1\) and \(g(u)\le u\) also for \(u=0,1\), we get

\[
h(r)=1+h(u)\le1+u\le g(r).
\]

Thus \(h(r)\le g(r)\). In particular, for \(r>1\),

\[
h(r)\le g(r)<r.
\]

Also \(h(0)=g(0)=0\), since \(g(0)\le1\).

It remains to prove monotonicity. We prove by strong induction on \(s\) that \(r\le s\) implies \(h(r)\le h(s)\). Let \(r\le s\), and set \(x=g(r)\), \(y=g(s)\). Since \(g\) is nondecreasing, \(x\le y\).

If \(y\le1\), then \(h(r)=x\le y=h(s)\). If \(y>1\) but \(x\le1\), then \(h(r)=x\le1\le h(s)\). If \(x>1\), put

\[
u=\lceil\log_2 x\rceil,
\qquad
v=\lceil\log_2 y\rceil.
\]

Then \(u\le v\), and \(v\le y-1<s\). By strong induction,

\[
h(u)\le h(v).
\]

Therefore

\[
h(r)=1+h(u)\le1+h(v)=h(s).
\]

So \(h\) is nondecreasing.

Finally, \(h\) is unbounded. We prove by induction on \(M\ge0\) that there is some \(r\) with \(h(r)\ge M\). For \(M=0\), any \(r\) works. Suppose this is known for \(M\), and choose \(u\) with \(h(u)\ge M\). Since \(g\) is unbounded, choose \(r\) with

\[
g(r)>2^u.
\]

Then \(g(r)>1\), and

\[
v=\lceil\log_2 g(r)\rceil>u.
\]

By monotonicity,

\[
h(v)\ge h(u)\ge M.
\]

Thus

\[
h(r)=1+h(v)\ge M+1.
\]

So \(h\) is unbounded.

#### Lemma 4.2: basic \(J_k\) package

For every \(k\ge0\):

1. \(J_k\) is integer-valued and nonnegative on \(\mathbb N\).
2. \(J_k(0)=0\).
3. \(J_k\) is nondecreasing.
4. \(J_k\) is unbounded on \(\mathbb N\).
5. \(J_k(r)<r\) for every \(r>1\).
6. \(J_{k+1}(r)\le J_k(r)\) for every \(r\ge0\).
7. \(R_k(t)\) is finite for every finite \(t\ge0\).
8. \(R_k(t)\) is nondecreasing in \(t\), and \(R_{k+1}(t)\ge R_k(t)\).

#### Proof

For \(k=0\),

\[
J_0(r)=\left\lceil\frac{r-1}{2}\right\rceil.
\]

This is integer-valued and nonnegative for integer \(r\ge0\). It satisfies \(J_0(0)=0\), is nondecreasing, is unbounded, and satisfies \(J_0(r)<r\) for \(r>1\).

Now assume \(J_k\) has properties 1--5. Apply Lemma 4.1 to \(g=J_k\). Since

\[
J_{k+1}=J_k^\diamond,
\]

the function \(J_{k+1}\) is integer-valued, nonnegative, nondecreasing, unbounded, satisfies \(J_{k+1}(0)=0\), and satisfies

\[
J_{k+1}(r)\le J_k(r)<r
\quad(r>1).
\]

This proves properties 1--6 by induction on \(k\).

Since \(J_k\) is unbounded and nondecreasing, the set

\[
\{r\ge0:J_k(r)\le t\}
\]

is finite for every finite \(t\ge0\). Since \(J_k(0)=0\le t\), it is also nonempty. Hence \(R_k(t)\) is a finite maximum.

If \(t\le t'\), then

\[
\{r:J_k(r)\le t\}\subseteq\{r:J_k(r)\le t'\},
\]

so \(R_k(t)\le R_k(t')\). Finally, since \(J_{k+1}(r)\le J_k(r)\),

\[
\{r:J_k(r)\le t\}\subseteq\{r:J_{k+1}(r)\le t\},
\]

so

\[
R_{k+1}(t)\ge R_k(t).
\]

This proves the package.

### 4.4 Exact base inverse

For \(J_0\),

\[
J_0(r)\le t
\]

if and only if

\[
r\le2t+1.
\]

Therefore

\[
R_0(t)=2t+1.
\]

### 4.5 Diamond-to-threshold recurrence

#### Lemma 4.3

Let \(B,t\) be nonnegative integers. If

\[
r\le R_k(2^B)
\]

and

\[
B\le R_{k+1}(t),
\]

then

\[
J_{k+1}(r)\le t+1.
\]

Consequently,

\[
R_{k+1}(t+1)\ge R_k(2^{R_{k+1}(t)}).
\]

#### Proof

Assume \(r\le R_k(2^B)\). Then

\[
J_k(r)\le2^B.
\]

If \(J_k(r)\le1\), then

\[
J_{k+1}(r)=J_k(r)\le1\le t+1.
\]

If \(J_k(r)>1\), then

\[
J_{k+1}(r)
=
1+J_{k+1}(\lceil\log_2J_k(r)\rceil).
\]

Since \(J_k(r)\le2^B\),

\[
\lceil\log_2J_k(r)\rceil\le B.
\]

By Lemma 4.2, \(J_{k+1}\) is nondecreasing. Since \(B\le R_{k+1}(t)\),

\[
J_{k+1}(\lceil\log_2J_k(r)\rceil)
\le
J_{k+1}(B)
\le t.
\]

Thus

\[
J_{k+1}(r)\le t+1.
\]

Therefore every \(r\le R_k(2^B)\) satisfies \(J_{k+1}(r)\le t+1\), and so

\[
R_{k+1}(t+1)\ge R_k(2^B).
\]

Taking \(B=R_{k+1}(t)\) proves

\[
R_{k+1}(t+1)\ge R_k(2^{R_{k+1}(t)}).
\]

### 4.6 Threshold jump

#### Lemma 4.4

For every \(k\ge0\) and every \(Q\ge2\),

\[
R_{k+1}(Q)\ge R_k(4Q).
\]

#### Proof

Apply Lemma 4.3 with \(t=Q-1\):

\[
R_{k+1}(Q)\ge R_k(2^{R_{k+1}(Q-1)}).
\]

By Lemma 4.2,

\[
R_{k+1}(Q-1)\ge R_0(Q-1)=2Q-1.
\]

For \(Q\ge2\),

\[
2^{2Q-1}\ge4Q.
\]

Using monotonicity of \(R_k\) from Lemma 4.2,

\[
R_{k+1}(Q)
\ge
R_k(2^{R_{k+1}(Q-1)})
\ge
R_k(4Q).
\]

### 4.7 Ackermann monotonicity and row domination

#### Lemma 4.5

For the packet Ackermann function:

1. for every \(i\ge0\), \(A(i,x)\) is nondecreasing in \(x\);
2. for every \(i\ge1\) and \(x\ge1\),

   \[
   A(i,x)\ge2x;
   \]

3. for every \(i\ge0\) and \(x\ge1\),

   \[
   A(i+1,x)\ge A(i,x).
   \]

#### Proof

For \(i=0\), monotonicity follows from \(A(0,x)=2x\).

For \(i\ge1\), monotonicity follows by induction on \(i\) and \(x\) from

\[
A(i,x+1)=A(i-1,A(i,x)).
\]

More explicitly, row \(i-1\) is nondecreasing, and \(A(i-1,y)\ge y\) for \(y\ge1\), so

\[
A(i,x+1)=A(i-1,A(i,x))\ge A(i,x).
\]

The growth bound is proved by induction on \(x\). For \(x=1\),

\[
A(i,1)=2=2x.
\]

For \(x\ge2\),

\[
A(i,x)=A(i-1,A(i,x-1)).
\]

If \(i=1\), this is \(2A(1,x-1)\). If \(i\ge2\), the lower-row growth bound gives at least \(2A(i,x-1)\). Hence

\[
A(i,x)\ge2A(i,x-1)\ge4(x-1)\ge2x.
\]

For row domination, fix \(i\ge0\). At \(x=1\),

\[
A(i+1,1)=2=A(i,1).
\]

For \(x\ge2\),

\[
A(i+1,x)=A(i,A(i+1,x-1)).
\]

The growth bound gives

\[
A(i+1,x-1)\ge2(x-1)\ge x.
\]

Since row \(i\) is nondecreasing,

\[
A(i+1,x)\ge A(i,x).
\]

### 4.8 Ackermann domination invariant

#### Lemma 4.6

For every \(j\ge1\) and \(x\ge1\),

\[
R_j(x)\ge A(j+1,x).
\]

#### Proof

We prove this by induction on \(j\), with an inner induction on \(x\).

First let \(j=1\). For \(x=1\), Lemma 4.3 with \(k=0,t=0\) gives

\[
R_1(1)\ge R_0(2^{R_1(0)}).
\]

By Lemma 4.2,

\[
R_1(0)\ge R_0(0)=1.
\]

Thus

\[
R_1(1)\ge R_0(2)=5\ge2=A(2,1).
\]

Assume \(R_1(x)\ge A(2,x)\). By Lemma 4.3,

\[
R_1(x+1)\ge R_0(2^{R_1(x)}).
\]

Since \(R_0(t)=2t+1\),

\[
R_0(2^{R_1(x)})=2\cdot2^{R_1(x)}+1.
\]

Using the induction hypothesis and \(A(1,y)=2^y\),

\[
2\cdot2^{R_1(x)}+1
\ge
2^{A(2,x)}
=
A(2,x+1).
\]

Thus the case \(j=1\) holds.

Now assume

\[
R_j(x)\ge A(j+1,x)
\]

for all \(x\ge1\). We prove

\[
R_{j+1}(x)\ge A(j+2,x)
\]

for all \(x\ge1\).

For \(x=1\), Lemma 4.2 gives

\[
R_{j+1}(1)\ge R_0(1)=3\ge2=A(j+2,1).
\]

Assume

\[
R_{j+1}(x)\ge A(j+2,x).
\]

By Lemma 4.3,

\[
R_{j+1}(x+1)\ge R_j(2^{R_{j+1}(x)}).
\]

By the outer induction hypothesis,

\[
R_j(y)\ge A(j+1,y)
\qquad(y\ge1).
\]

Thus

\[
R_j(2^{R_{j+1}(x)})
\ge
A(j+1,2^{R_{j+1}(x)}).
\]

Since

\[
2^{R_{j+1}(x)}
\ge
R_{j+1}(x)
\ge
A(j+2,x),
\]

Ackermann monotonicity gives

\[
A(j+1,2^{R_{j+1}(x)})
\ge
A(j+1,A(j+2,x)).
\]

By the Ackermann recursion,

\[
A(j+2,x+1)
=
A(j+1,A(j+2,x)).
\]

Therefore

\[
R_{j+1}(x+1)\ge A(j+2,x+1).
\]

This completes the induction.

### 4.9 Main comparison theorem

#### Theorem 4.7

For all integers \(z\ge1\) and \(Q\ge1\),

\[
R_{z+1}(Q)\ge A(z,4Q).
\]

Consequently,

\[
A(z,4Q)>r
\quad\Longrightarrow\quad
J_{z+1}(r)\le Q.
\]

#### Proof

First suppose \(Q\ge2\). By Lemma 4.4,

\[
R_{z+1}(Q)\ge R_z(4Q).
\]

Since \(z\ge1\), Lemma 4.6 gives

\[
R_z(4Q)\ge A(z+1,4Q).
\]

By row domination from Lemma 4.5,

\[
A(z+1,4Q)\ge A(z,4Q).
\]

Therefore

\[
R_{z+1}(Q)\ge A(z,4Q).
\]

Now suppose \(Q=1,z=1\). Lemma 4.3 gives

\[
R_2(1)\ge R_1(2^{R_2(0)}).
\]

By Lemma 4.2, \(R_2(0)\ge R_0(0)=1\), so

\[
R_2(1)\ge R_1(2).
\]

The proof of Lemma 4.6 gave \(R_1(1)\ge5\), and Lemma 4.3 gives

\[
R_1(2)\ge R_0(2^{R_1(1)})\ge R_0(2^5)=65.
\]

Hence

\[
R_2(1)\ge65\ge16=A(1,4).
\]

Finally suppose \(Q=1,z\ge2\). Lemma 4.3 gives

\[
R_{z+1}(1)\ge R_z(2^{R_{z+1}(0)}).
\]

By Lemma 4.2, \(R_{z+1}(0)\ge R_0(0)=1\), so

\[
R_{z+1}(1)\ge R_z(2).
\]

Apply Lemma 4.4 with level \(z-1\) and \(Q=2\):

\[
R_z(2)\ge R_{z-1}(8).
\]

Since \(z-1\ge1\), Lemma 4.6 gives

\[
R_{z-1}(8)\ge A(z,8).
\]

By Ackermann monotonicity,

\[
A(z,8)\ge A(z,4).
\]

Thus

\[
R_{z+1}(1)\ge A(z,4).
\]

Combining the three cases proves

\[
R_{z+1}(Q)\ge A(z,4Q).
\]

If \(A(z,4Q)>r\), then \(r\le A(z,4Q)-1\le R_{z+1}(Q)\), and hence

\[
J_{z+1}(r)\le Q.
\]

---

## 5. Alpha consequences and cost bound

### 5.1 Packet alpha definitions

Define

\[
\alpha_J^Q(m,n)=\min\{k\ge0:J_k(L(n))\le Q(m,n)\},
\]

and

\[
\alpha_Q(m,n)=\min\{z\ge1:A(z,4Q(m,n))>L(n)\}.
\]

This minimum exists. Since \(Q(m,n)\ge1\), we have \(4Q(m,n)\ge4\). Let \(a_z=A(z,4)\). Then \(a_1=16\), and for \(z\ge1\),

\[
A(z+1,2)=4,\qquad A(z+1,3)=A(z,4)=a_z,
\]

so

\[
a_{z+1}=A(z+1,4)=A(z,a_z).
\]

By the growth bound in Lemma 4.5, \(A(z,a_z)\ge2a_z\). Hence \(a_z\) is unbounded in \(z\). By monotonicity in the second argument,

\[
A(z,4Q(m,n))\ge A(z,4)=a_z,
\]

so some \(z\ge1\) satisfies \(A(z,4Q(m,n))>L(n)\).

### 5.2 Patched threshold theorem

#### Theorem 5.1

For all positive integers \(m,n\),

\[
\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1.
\]

#### Proof

Let

\[
z=\alpha_Q(m,n),
\qquad
Q=Q(m,n),
\qquad
L=L(n).
\]

By definition,

\[
A(z,4Q)>L.
\]

By Theorem 4.7,

\[
R_{z+1}(Q)\ge A(z,4Q)>L.
\]

Since \(L\) is an integer,

\[
L\le R_{z+1}(Q).
\]

Therefore

\[
J_{z+1}(L)\le Q.
\]

Hence

\[
\alpha_J^Q(m,n)\le z+1=\alpha_Q(m,n)+1.
\]

### 5.3 Source-faithful real threshold

Define

\[
\alpha_J^S(m,n)=
\min\left\{k\ge0:J_k(L(n))\le1+\frac mn\right\}.
\]

#### Lemma 5.2: Ackermann buffer

For \(z\ge1\) and integer \(p\ge1\),

\[
A(z+1,4p)\ge A(z,4p+4).
\]

#### Proof

Since \(4p\ge2\),

\[
A(z+1,4p)=A(z,A(z+1,4p-1)).
\]

We claim

\[
A(z+1,4p-1)\ge4p+4.
\]

If \(p=1\), then \(4p-1=3\), and \(A(i,2)=4\) for all \(i\ge1\), so

\[
A(z+1,3)=A(z,4)\ge8=4p+4.
\]

If \(p\ge2\), Lemma 4.5 gives

\[
A(z+1,4p-1)\ge2(4p-1)=8p-2\ge4p+4.
\]

By monotonicity of \(A(z,-)\),

\[
A(z+1,4p)\ge A(z,4p+4).
\]

#### Theorem 5.3

For all positive integers \(m,n\),

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+2.
\]

If \(1+m/n\) is integral, then

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+1.
\]

#### Proof

Let

\[
s=1+\frac mn,
\qquad
Q=\lceil s\rceil,
\qquad
L=L(n),
\qquad
z=\alpha_Q(m,n).
\]

Then

\[
A(z,4Q)>L.
\]

If \(s\) is integral, \(Q=s\). Theorem 4.7 gives

\[
R_{z+1}(s)\ge A(z,4Q)>L,
\]

so

\[
J_{z+1}(L)\le s.
\]

Hence

\[
\alpha_J^S(m,n)\le z+1=\alpha_Q(m,n)+1.
\]

If \(s\) is not integral, put \(p=\lfloor s\rfloor\). Since \(m,n\ge1\), \(p\ge1\), and \(Q=p+1\). Thus

\[
A(z,4p+4)>L.
\]

By Lemma 5.2,

\[
A(z+1,4p)>L.
\]

Theorem 4.7 gives

\[
R_{z+2}(p)\ge A(z+1,4p)>L,
\]

so

\[
J_{z+2}(L)\le p<s.
\]

Therefore

\[
\alpha_J^S(m,n)\le z+2=\alpha_Q(m,n)+2.
\]

### 5.4 Cost consequence

#### Theorem 5.4

Using the source recurrence

\[
f(m,n,r)\le km+2nJ_k(r),
\]

one obtains

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n.
\]

Consequently,

\[
f(m,n,L(n))=O(m\alpha_Q(m,n)+n).
\]

#### Proof

Let

\[
z=\alpha_Q(m,n),
\qquad
Q=Q(m,n),
\qquad
L=L(n).
\]

By Theorem 5.1,

\[
J_{z+1}(L)\le Q.
\]

Apply the recurrence with \(k=z+1\) and \(r=L\):

\[
f(m,n,L)
\le
(z+1)m+2nJ_{z+1}(L)
\le
(z+1)m+2nQ.
\]

Since

\[
Q=\left\lceil1+\frac mn\right\rceil
\le
2+\frac mn,
\]

we have

\[
2nQ\le 2n\left(2+\frac mn\right)=4n+2m.
\]

Therefore

\[
f(m,n,L)
\le
(z+3)m+4n.
\]

Substituting \(z=\alpha_Q(m,n)\) gives

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n.
\]

---

## 6. Dependency table and DAG

| stage | input | output |
|---|---|---|
| source definitions | \(g^*\), \(g^\diamond\), \(J_0\), \(J_{k+1}=J_k^\diamond\) | the `J` hierarchy |
| source recurrence | shifting lemma with \(2ng(r)\) premise | \(f(m,n,r)\le km+2nJ_k(r)\) |
| basic \(J\) lemmas | diamond preservation | \(J_k\) monotone, unbounded, \(J_k(r)<r\), finite \(R_k\) |
| threshold recurrence | \(J_{k+1}=J_k^\diamond\) | \(R_{k+1}(t+1)\ge R_k(2^{R_{k+1}(t)})\) |
| Ackermann domination | threshold recurrence plus \(R_0(t)=2t+1\) | \(R_j(x)\ge A(j+1,x)\) |
| main comparison | threshold jump and row domination | \(R_{z+1}(Q)\ge A(z,4Q)\) |
| alpha translation | \(A(z,4Q)>L(n)\) | \(\alpha_J^Q\le\alpha_Q+1\), \(\alpha_J^S\le\alpha_Q+2\) |
| cost bound | recurrence \(f\le km+2nJ_k\) | \(f(m,n,L(n))\le(\alpha_Q+3)m+4n\) |

DAG form:

```text
source definitions
  -> J hierarchy
  -> basic J lemmas
  -> threshold recurrence
  -> Ackermann domination
  -> R/Ackermann comparison
  -> alpha consequences
  -> cost bound

source shifting lemma
  -> recurrence f(m,n,r) <= k m + 2n J_k(r)
  -> cost bound
```

---

## 7. Normalization appendix

This note proves the packet-normalized theorem. It does not assert a universal comparison with every inverse-Ackermann convention.

### 7.1 Classical row-inverse convention for this note

Define the classical row-inverse for the packet Ackermann normalization by

\[
\alpha_A(N,X)=\min\{z\ge1:A(z,X)>N\}.
\]

Then the packet inverse is exactly

\[
\alpha_Q(m,n)=\alpha_A(L(n),4Q(m,n)).
\]

This is a concrete classical inverse-Ackermann convention: rows are indexed by \(z\), and the second input is a threshold parameter.

### 7.2 Comparison with \(\alpha_J^Q\)

The patched \(J\)-threshold inverse is

\[
\alpha_J^Q(m,n)=\min\{k\ge0:J_k(L(n))\le Q(m,n)\}.
\]

The proved comparison gives

\[
\alpha_J^Q(m,n)
\le
\alpha_A(L(n),4Q(m,n))+1.
\]

Equivalently,

\[
\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1.
\]

### 7.3 Comparison with \(\alpha_J^S\)

The source-faithful \(J\)-threshold inverse is

\[
\alpha_J^S(m,n)=
\min\left\{k\ge0:J_k(L(n))\le1+\frac mn\right\}.
\]

The proved comparison gives

\[
\alpha_J^S(m,n)
\le
\alpha_A(L(n),4Q(m,n))+2.
\]

If \(1+m/n\) is integral, then \(Q(m,n)=1+m/n\), and the sharper comparison is

\[
\alpha_J^S(m,n)
\le
\alpha_A(L(n),4Q(m,n))+1.
\]

### 7.4 Relation to the source \(\alpha_S\)

The source defines

\[
\alpha_S(m,n)=
\min\left\{k:J_k(\lceil\log_2 n\rceil)\le1+\frac mn\right\}.
\]

For \(n\ge2\),

\[
L(n)=\lceil\log_2 n\rceil,
\]

so \(\alpha_J^S\) is the packet notation for the source \(\alpha_S\). For \(n=1\), the packet uses \(L(1)=1\) rather than \(0\), a harmless stabilization for the proof note.

### 7.5 Named external convention: Tarjan-style \(\alpha_T\)

The Seidel--Sharir source discusses Tarjan's initial inverse-Ackermann function \(\alpha_T\), defined via a different hierarchy \(T_k\), and states that the differences between \(\alpha_S\) and \(\alpha_T\) are minor/asymptotically equivalent. This v2 note does **not** use that comparison as a theorem dependency. The theorem here is restricted to the concrete packet normalization

\[
\alpha_Q(m,n)=\alpha_A(L(n),4Q(m,n)).
\]

Thus the result is source-faithful and concrete without relying on an informal “all inverse-Ackermanns differ by constants” claim.

---

## 8. Hazards avoided

### 8.1 \(1+m/n\) versus \(2m/n\)

The source-faithful \(J\)-threshold in the recovered source anchor is

\[
J_k(\lceil\log_2 n\rceil)\le1+\frac mn,
\]

not a \(J_k\)-threshold \(2m/n\). The alternate condition

\[
J_k(\lg n)\le \frac{2m}{n}
\]

is not source-faithful under the current packet unless independently verified. It is also impossible for \(m/n<1/2\) and \(n\ge3\), because then it would force \(J_k(L(n))=0\) while \(J_k(r)\ge1\) for \(r\ge2\).

### 8.2 The factor \(2n\) in the shifting lemma

The source shifting lemma has premise

\[
f(m,n,r)\le km+2ng(r)
\]

and conclusion

\[
f(m,n,r)\le(k+1)m+2n g^\diamond(r).
\]

The v2 note uses this source-correct statement. The earlier shorthand with \(ng(r)\) was a source-fidelity wording mismatch and is not used here.

### 8.3 Why \(Q(m,n)=\lceil1+m/n\rceil\) is used

The comparison theorem is naturally stated for an integer threshold \(Q\ge1\). The source threshold \(1+m/n\) is real-valued. The packet threshold

\[
Q(m,n)=\left\lceil1+\frac mn\right\rceil
\]

provides an integer target for the \(R_k\) comparison. The exact real source threshold is recovered with an extra \(+1\) buffer in the nonintegral case.

### 8.4 Avoiding bottom-up Tarjan-potential drift

The proof uses only:

1. the Seidel--Sharir top-down \(J\) hierarchy;
2. the \(g^\diamond\) threshold recurrence;
3. the packet Ackermann normalization;
4. the source recurrence \(f(m,n,r)\le km+2nJ_k(r)\).

It does not use bottom-up Tarjan potentials, lower bounds, implementation-specific union-find details, or a broad inverse-Ackermann literature comparison.

---

## 9. What is new here?

This note does not claim a new union-find bound. It gives a direct, source-anchored proof that the Seidel--Sharir top-down \(J\) hierarchy implies an inverse-Ackermann bound under an explicit Ackermann normalization, addressing Tarjan's Dagstuhl comparison problem at the level of proof exposition and digestion.

## 10. Final theorem block suitable for citation

```text
Final theorem block: top-down J hierarchy implies the packet-normalized inverse-Ackermann bound.

Assume the packet/source definitions

    J_0(r) = ceil((r-1)/2),
    J_{k+1} = J_k^diamond,

where

    g^diamond(r) = g(r)                                      if g(r) <= 1,
    g^diamond(r) = 1 + g^diamond(ceil(log_2 g(r)))            if g(r) > 1.

Define

    R_k(t) = max { r >= 0 : J_k(r) <= t }.

For each fixed k, J_k is unbounded on N, so R_k(t) is finite for finite t.

With the packet Ackermann normalization

    A(0,x) = 2x,
    A(i,0) = 0  for i >= 1,
    A(i,1) = 2  for i >= 1,
    A(i,x) = A(i-1,A(i,x-1))  for i >= 1, x >= 2,

one has, for all z >= 1 and Q >= 1,

    R_{z+1}(Q) >= A(z,4Q).

Thus the coordinator comparison target holds with

    c = 1,
    C = 1,
    D = 4.

Let

    L(n) = ceil(log_2 max(n,2)),
    Q(m,n) = ceil(1 + m/n),

and define

    alpha_Q(m,n)
      = min { z >= 1 : A(z,4Q(m,n)) > L(n) },

    alpha_J^Q(m,n)
      = min { k >= 0 : J_k(L(n)) <= Q(m,n) }.

Then

    alpha_J^Q(m,n) <= alpha_Q(m,n)+1.

For the current packet's source-faithful threshold

    J_k(L(n)) <= 1 + m/n,

define

    alpha_J^S(m,n)
      = min { k >= 0 : J_k(L(n)) <= 1 + m/n }.

Then

    alpha_J^S(m,n) <= alpha_Q(m,n)+2.

If 1 + m/n is integral, then the sharper bound holds:

    alpha_J^S(m,n) <= alpha_Q(m,n)+1.

Using the source recurrence

    f(m,n,r) <= k m + 2n J_k(r),

this gives

    f(m,n,L(n)) <= (alpha_Q(m,n)+3)m + 4n,

and hence

    f(m,n,L(n)) = O(m alpha_Q(m,n) + n).

The alternate threshold J_k(lg n) <= 2m/n is not source-faithful under the current packet unless independently verified from the paper.
```

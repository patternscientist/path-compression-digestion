# Final frontier/proof note: top-down `J` hierarchy implies the classical inverse-Ackermann bound under packet conventions

## 1. Executive summary

This note packages the complete proof chain, under the packet conventions, that the Seidel--Sharir top-down path-compression `J` hierarchy implies a classical inverse-Ackermann bound.

The central threshold inverse is

\[
R_k(t)=\max\{r\ge 0:J_k(r)\le t\}.
\]

In the packet setting, the functions \(J_k\) are unbounded on \(\mathbb N\), so this maximum is finite; equivalently, \(R_k\) is the finite threshold inverse of \(J_k\).

The hard comparison theorem proved from the packet’s `J` hierarchy is:

\[
R_{z+1}(Q)\ge A(z,4Q)
\qquad
(z\ge 1,\ Q\ge 1).
\]

Equivalently,

\[
A(z,4Q)>r
\quad\Longrightarrow\quad
J_{z+1}(r)\le Q.
\]

Thus the constants in the coordinator target

\[
R_{cz+C}(Q)\ge A(z,DQ)
\]

are

\[
c=1,\qquad C=1,\qquad D=4.
\]

With

\[
L(n)=\lceil \log_2 \max(n,2)\rceil,
\qquad
Q(m,n)=\left\lceil 1+\frac mn\right\rceil,
\]

and

\[
\alpha_Q(m,n)=\min\{z\ge 1:A(z,4Q(m,n))>L(n)\},
\]

the patched integer threshold satisfies

\[
\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1,
\]

where

\[
\alpha_J^Q(m,n)=\min\{k\ge 0:J_k(L(n))\le Q(m,n)\}.
\]

Using the packet recurrence bound

\[
f(m,n,r)\le km+2nJ_k(r),
\]

this gives

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n
=
O(m\alpha_Q(m,n)+n).
\]

The current packet’s source anchor records the source inverse threshold as

\[
J_k(\lceil \log_2 n\rceil)\le 1+\frac mn.
\]

For this source-faithful real threshold, define

\[
\alpha_J^S(m,n)
=
\min\left\{k\ge 0:J_k(L(n))\le 1+\frac mn\right\}.
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

The alternate threshold

\[
J_k(\lg n)\le \frac{2m}{n}
\]

is not source-faithful under the current packet unless independently rechecked against the paper. Under the packet definitions it is a stricter alternate target, and it is impossible in the low-load range \(m/n<1/2\), \(n\ge 3\).

---

## 2. Source-fidelity block

This section records the precise packet definitions and source-normalization conventions used below. It is not a new literature review and does not rederive the top-down path-compression recurrence.

### 2.1 The functions \(g^*\) and \(g^\diamond\)

For an admissible integer-valued function \(g\), the source-style iteration count is

\[
g^*(r)=\min\{t\ge 0:g^{(t)}(r)\le 1\}.
\]

The packet’s sharper recursive transform is

\[
g^\diamond(r)=
\begin{cases}
g(r),& g(r)\le 1,\\[4pt]
1+g^\diamond(\lceil \log_2 g(r)\rceil),& g(r)>1.
\end{cases}
\]

All logarithms in this note are base \(2\).

### 2.2 The \(J\) hierarchy

The packet defines

\[
J_0(r)=\left\lceil \frac{r-1}{2}\right\rceil,
\]

and recursively

\[
J_{k+1}=J_k^\diamond.
\]

Thus

\[
J_{k+1}(r)
=
\begin{cases}
J_k(r),& J_k(r)\le 1,\\[4pt]
1+J_{k+1}(\lceil \log_2 J_k(r)\rceil),& J_k(r)>1.
\end{cases}
\]

### 2.3 Shifting lemma and recurrence bound

The packet source-fidelity pass records the top-down shifting lemma in the following form:

If

\[
f(m,n,r)\le km+ng(r),
\]

then

\[
f(m,n,r)\le (k+1)m+2n g^\diamond(r).
\]

Iterating this with the \(J\) hierarchy gives the recurrence consequence

\[
f(m,n,r)\le km+2nJ_k(r).
\]

This recurrence is used only after the threshold comparison has produced a \(k\) for which \(J_k(L(n))\) is small.

### 2.4 Source inverse threshold

The current packet’s source anchor records the Seidel--Sharir inverse threshold as

\[
J_k(\lceil \log_2 n\rceil)\le 1+\frac mn.
\]

The packet rank cutoff is

\[
L(n)=\lceil \log_2 \max(n,2)\rceil.
\]

For \(n\ge 2\), this agrees with \(\lceil \log_2 n\rceil\). For \(n=1\), it replaces the degenerate cutoff \(0\) by \(1\).

### 2.5 Patched integer threshold

The patched integer threshold is

\[
Q(m,n)=\left\lceil 1+\frac mn\right\rceil.
\]

This is useful because the comparison theorem is stated for integer thresholds \(Q\ge 1\), while the source threshold \(1+m/n\) is generally real-valued.

---

## 3. Closed comparison theorem

This section proves the hard comparison theorem self-containedly from the packet’s \(J\) hierarchy and the Ackermann normalization below.

### 3.1 Ackermann normalization

The packet Ackermann function is

\[
A(0,x)=2x,
\]

and for \(i\ge 1\),

\[
A(i,0)=0,
\qquad
A(i,1)=2,
\qquad
A(i,x)=A(i-1,A(i,x-1))\quad (x\ge 2).
\]

In particular,

\[
A(1,x)=2^x
\]

for \(x\ge 1\). This follows from \(A(1,1)=2\) and

\[
A(1,x+1)=A(0,A(1,x))=2A(1,x).
\]

### 3.2 Threshold inverse

For integer \(t\ge 0\), define

\[
R_k(t)=\max\{r\ge 0:J_k(r)\le t\}.
\]

In the packet setting, the functions \(J_k\) are unbounded on \(\mathbb N\), so this maximum is finite; equivalently, \(R_k\) is the finite threshold inverse of \(J_k\).

The goal is to prove

\[
R_{z+1}(Q)\ge A(z,4Q)
\qquad
(z\ge 1,\ Q\ge 1).
\]

### 3.3 Basic properties of \(J_k\) and \(R_k\)

This subsection supplies the elementary \(J\)-facts used later in Lemmas 3.1--3.3.

For \(J_0\),

\[
J_0(r)=\left\lceil \frac{r-1}{2}\right\rceil.
\]

Thus

\[
J_0(r)\le t
\]

if and only if

\[
r\le 2t+1.
\]

Therefore

\[
R_0(t)=2t+1.
\]

We now prove the closure properties of the diamond operation needed below.

#### Lemma 3.0: diamond preservation lemma

Let \(g:\mathbb N\to\mathbb N\) be integer-valued, nonnegative, nondecreasing, and satisfy

\[
g(r)\le r
\qquad (r\ge 0).
\]

Define \(h=g^\diamond\) by

\[
h(r)=
\begin{cases}
g(r),& g(r)\le 1,\\[4pt]
1+h(\lceil \log_2 g(r)\rceil),& g(r)>1.
\end{cases}
\]

Then \(h\) is integer-valued, nonnegative, nondecreasing, and satisfies

\[
h(r)\le g(r)\le r
\qquad (r\ge 0).
\]

#### Proof

First note the elementary estimate: if \(x\ge 2\) is an integer, then

\[
\lceil \log_2 x\rceil\le x-1.
\]

Indeed this is equality for \(x=2\), and for \(x\ge 3\) it follows from \(\log_2 x\le x-1\). Hence, in the recursive branch \(g(r)>1\), with

\[
u=\lceil \log_2 g(r)\rceil,
\]

we have

\[
u\le g(r)-1\le r-1.
\]

So the recursion defining \(h(r)\) only calls \(h\) on smaller arguments. Thus \(h\) is well-defined by induction on \(r\), and it is integer-valued and nonnegative because \(g\) is.

We next prove

\[
h(r)\le g(r)
\]

by induction on \(r\). If \(g(r)\le 1\), then \(h(r)=g(r)\). If \(g(r)>1\), set

\[
u=\lceil \log_2 g(r)\rceil.
\]

Then \(u<r\), so by induction,

\[
h(u)\le g(u).
\]

Since \(g(u)\le u\), we get

\[
h(r)=1+h(u)\le 1+u\le g(r).
\]

Thus \(h(r)\le g(r)\le r\).

It remains to prove that \(h\) is nondecreasing. We prove, by strong induction on \(s\), that for every \(r\le s\),

\[
h(r)\le h(s).
\]

Let \(r\le s\), and write

\[
x=g(r),
\qquad
 y=g(s).
\]

Since \(g\) is nondecreasing, \(x\le y\).

If \(y\le 1\), then also \(x\le 1\), so

\[
h(r)=x\le y=h(s).
\]

Now suppose \(y>1\). If \(x\le 1\), then

\[
h(r)=x\le 1\le h(s),
\]

because in the branch \(y>1\),

\[
h(s)=1+h(\lceil\log_2 y\rceil)\ge 1.
\]

Finally suppose \(x>1\). Put

\[
u=\lceil\log_2 x\rceil,
\qquad
v=\lceil\log_2 y\rceil.
\]

Then \(u\le v\). Also

\[
v\le y-1\le s-1,
\]

so the strong induction hypothesis applies to \(u\le v<s\). Hence

\[
h(u)\le h(v).
\]

Therefore

\[
h(r)=1+h(u)\le 1+h(v)=h(s).
\]

This proves that \(h\) is nondecreasing.

#### Lemma 3.0A: basic \(J\)-lemma package

For every \(k\ge 0\):

1. \(J_k\) is integer-valued and nonnegative on \(r\ge 0\).
2. \(J_k\) is nondecreasing in \(r\).
3. \(J_k(r)\le r\) for all \(r\ge 0\).
4. \(J_{k+1}(r)\le J_k(r)\) for all \(r\ge 0\).
5. Hence \(R_k(t)\) is nondecreasing in \(t\), and
   \[
   R_{k+1}(t)\ge R_k(t)
   \]
   for all \(k,t\).

#### Proof

For \(k=0\),

\[
J_0(r)=\left\lceil \frac{r-1}{2}\right\rceil.
\]

This is integer-valued, nonnegative for integer \(r\ge 0\), nondecreasing in \(r\), and satisfies

\[
J_0(r)\le r
\]

for all \(r\ge 0\).

Assume now that \(J_k\) is integer-valued, nonnegative, nondecreasing, and satisfies \(J_k(r)\le r\). Apply Lemma 3.0 to \(g=J_k\). Since

\[
J_{k+1}=J_k^\diamond,
\]

Lemma 3.0 gives that \(J_{k+1}\) is integer-valued, nonnegative, nondecreasing, and satisfies

\[
J_{k+1}(r)\le J_k(r)\le r.
\]

This proves the first four claims by induction on \(k\).

For the threshold inverse, if \(t\le t'\), then

\[
\{r:J_k(r)\le t\}\subseteq \{r:J_k(r)\le t'\},
\]

so

\[
R_k(t)\le R_k(t').
\]

Thus \(R_k(t)\) is nondecreasing in \(t\).

Finally, since \(J_{k+1}(r)\le J_k(r)\), we have

\[
\{r:J_k(r)\le t\}\subseteq \{r:J_{k+1}(r)\le t\}.
\]

Therefore

\[
R_{k+1}(t)\ge R_k(t).
\]

This proves the lemma package.

### 3.4 Diamond-to-threshold recurrence

#### Lemma 3.1

If

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

Let

\[
h=J_{k+1}=J_k^\diamond.
\]

Assume

\[
r\le R_k(2^B).
\]

Then

\[
J_k(r)\le 2^B.
\]

If \(J_k(r)\le 1\), then by the definition of \(g^\diamond\),

\[
J_{k+1}(r)=J_k(r)\le 1\le t+1.
\]

Now suppose \(J_k(r)>1\). Then

\[
J_{k+1}(r)
=
1+J_{k+1}(\lceil \log_2 J_k(r)\rceil).
\]

Since

\[
J_k(r)\le 2^B,
\]

we have

\[
\lceil \log_2 J_k(r)\rceil\le B.
\]

By Lemma 3.0A, \(J_{k+1}\) is nondecreasing. Since \(B\le R_{k+1}(t)\), we get

\[
J_{k+1}(\lceil \log_2 J_k(r)\rceil)
\le
J_{k+1}(B)
\le t.
\]

Therefore

\[
J_{k+1}(r)\le t+1.
\]

Thus every \(r\le R_k(2^B)\) satisfies \(J_{k+1}(r)\le t+1\), so

\[
R_{k+1}(t+1)\ge R_k(2^B).
\]

Taking \(B=R_{k+1}(t)\) gives

\[
R_{k+1}(t+1)\ge R_k(2^{R_{k+1}(t)}).
\]

This proves the lemma.

### 3.5 Threshold jump

#### Lemma 3.2

For every \(k\ge 0\) and every \(Q\ge 2\),

\[
R_{k+1}(Q)\ge R_k(4Q).
\]

#### Proof

Apply Lemma 3.1 with \(t=Q-1\):

\[
R_{k+1}(Q)\ge R_k(2^{R_{k+1}(Q-1)}).
\]

By Lemma 3.0A, \(R_{k+1}(Q-1)\ge R_0(Q-1)\). Using \(R_0(t)=2t+1\),

\[
R_0(Q-1)=2Q-1.
\]

Thus

\[
2^{R_{k+1}(Q-1)}
\ge
2^{2Q-1}.
\]

For \(Q\ge 2\),

\[
2^{2Q-1}\ge 4Q.
\]

Therefore, using monotonicity of \(R_k\) in its threshold argument from Lemma 3.0A,

\[
R_{k+1}(Q)
\ge
R_k(2^{R_{k+1}(Q-1)})
\ge
R_k(4Q).
\]

This proves the threshold jump.

### 3.6 Ackermann monotonicity and row domination

#### Lemma 3.2A

For the packet Ackermann function:

1. For every \(i\ge 0\), \(A(i,x)\) is nondecreasing in \(x\).
2. For every \(i\ge 1\) and \(x\ge 1\),
   \[
   A(i,x)\ge 2x.
   \]
3. For every \(i\ge 0\) and \(x\ge 1\),
   \[
   A(i+1,x)\ge A(i,x).
   \]

#### Proof

We first prove the first two assertions together by induction on \(i\).

For \(i=0\), monotonicity is immediate from

\[
A(0,x)=2x.
\]

Now let \(i\ge 1\), and assume the needed facts for lower rows. We prove monotonicity of row \(i\). Since

\[
A(i,0)=0
\qquad\text{and}\qquad
A(i,1)=2,
\]

we have \(A(i,0)\le A(i,1)\). For \(x\ge 1\),

\[
A(i,x+1)=A(i-1,A(i,x)).
\]

If \(i=1\), then \(A(0,y)=2y\ge y\), so

\[
A(1,x+1)=A(0,A(1,x))\ge A(1,x).
\]

If \(i\ge 2\), then by the growth assertion for row \(i-1\),

\[
A(i-1,y)\ge 2y\ge y
\qquad (y\ge 1).
\]

Applying this to \(y=A(i,x)\), we again get

\[
A(i,x+1)\ge A(i,x).
\]

Thus row \(i\) is nondecreasing.

We next prove the growth bound for row \(i\ge 1\). For \(x=1\),

\[
A(i,1)=2=2x.
\]

For \(x\ge 2\), use induction on \(x\). If \(i=1\), then

\[
A(1,x)=A(0,A(1,x-1))=2A(1,x-1).
\]

If \(i\ge 2\), then the growth bound for row \(i-1\) gives

\[
A(i,x)=A(i-1,A(i,x-1))\ge 2A(i,x-1).
\]

In either case, by the inner induction hypothesis,

\[
A(i,x)\ge 2A(i,x-1)\ge 4(x-1)\ge 2x.
\]

This proves both monotonicity in \(x\) and the growth bound.

It remains to prove row domination. Fix \(i\ge 0\). For \(x=1\),

\[
A(i+1,1)=2=A(i,1),
\]

where for \(i=0\), \(A(0,1)=2\) as well. For \(x\ge 2\),

\[
A(i+1,x)=A(i,A(i+1,x-1)).
\]

By the growth bound just proved for row \(i+1\),

\[
A(i+1,x-1)\ge 2(x-1)\ge x.
\]

Since row \(i\) is nondecreasing in its second argument,

\[
A(i,A(i+1,x-1))\ge A(i,x).
\]

Therefore

\[
A(i+1,x)\ge A(i,x).
\]

This proves row domination.

### 3.7 Ackermann domination invariant

#### Lemma 3.3

For every \(j\ge 1\) and every \(x\ge 1\),

\[
R_j(x)\ge A(j+1,x).
\]

#### Proof

We prove the claim by induction on \(j\), with an inner induction on \(x\).

First take \(j=1\).

For \(x=1\), Lemma 3.1 with \(k=0,t=0\) gives

\[
R_1(1)\ge R_0(2^{R_1(0)}).
\]

By Lemma 3.0A,

\[
R_1(0)\ge R_0(0)=1.
\]

Hence

\[
R_1(1)\ge R_0(2)=5.
\]

Also

\[
A(2,1)=2.
\]

Thus

\[
R_1(1)\ge A(2,1).
\]

Now assume

\[
R_1(x)\ge A(2,x).
\]

Again using Lemma 3.1,

\[
R_1(x+1)\ge R_0(2^{R_1(x)}).
\]

Since \(R_0(t)=2t+1\),

\[
R_0(2^{R_1(x)})
=
2\cdot 2^{R_1(x)}+1.
\]

By the induction hypothesis,

\[
R_1(x)\ge A(2,x),
\]

so

\[
2\cdot 2^{R_1(x)}+1
\ge
2^{A(2,x)}.
\]

Because \(A(1,y)=2^y\),

\[
A(2,x+1)
=
A(1,A(2,x))
=
2^{A(2,x)}.
\]

Therefore

\[
R_1(x+1)\ge A(2,x+1).
\]

This proves the case \(j=1\).

Now assume for some \(j\ge 1\) that

\[
R_j(x)\ge A(j+1,x)
\]

for every \(x\ge 1\). We prove

\[
R_{j+1}(x)\ge A(j+2,x)
\]

for every \(x\ge 1\).

For \(x=1\),

\[
A(j+2,1)=2.
\]

Also, by Lemma 3.0A,

\[
R_{j+1}(1)\ge R_0(1)=3.
\]

Thus

\[
R_{j+1}(1)\ge A(j+2,1).
\]

Now assume

\[
R_{j+1}(x)\ge A(j+2,x).
\]

By Lemma 3.1,

\[
R_{j+1}(x+1)
\ge
R_j(2^{R_{j+1}(x)}).
\]

By the outer induction hypothesis,

\[
R_j(y)\ge A(j+1,y)
\]

for every \(y\ge 1\). Hence

\[
R_j(2^{R_{j+1}(x)})
\ge
A(j+1,2^{R_{j+1}(x)}).
\]

Since \(2^u\ge u\) for every integer \(u\ge 0\),

\[
2^{R_{j+1}(x)}
\ge
R_{j+1}(x)
\ge
A(j+2,x).
\]

By Ackermann monotonicity in the second argument from Lemma 3.2A,

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

This completes the induction and proves the lemma.

### 3.8 Main comparison theorem

#### Theorem 3.4

For all integers \(z\ge 1\) and \(Q\ge 1\),

\[
R_{z+1}(Q)\ge A(z,4Q).
\]

Equivalently,

\[
A(z,4Q)>r
\quad\Longrightarrow\quad
J_{z+1}(r)\le Q.
\]

#### Proof

We split into cases.

##### Case 1: \(Q\ge 2\)

By Lemma 3.2,

\[
R_{z+1}(Q)\ge R_z(4Q).
\]

Since \(z\ge 1\), Lemma 3.3 gives

\[
R_z(4Q)\ge A(z+1,4Q).
\]

By row domination for Ackermann from Lemma 3.2A,

\[
A(z+1,4Q)\ge A(z,4Q).
\]

Therefore

\[
R_{z+1}(Q)\ge A(z,4Q).
\]

##### Case 2: \(Q=1\), \(z=1\)

We need

\[
R_2(1)\ge A(1,4)=16.
\]

By Lemma 3.1 with \(k=1,t=0\),

\[
R_2(1)\ge R_1(2^{R_2(0)}).
\]

By Lemma 3.0A,

\[
R_2(0)\ge R_0(0)=1.
\]

Thus

\[
R_2(1)\ge R_1(2).
\]

Also, as shown in the proof of Lemma 3.3,

\[
R_1(1)\ge 5.
\]

Applying Lemma 3.1 with \(k=0,t=1\),

\[
R_1(2)
\ge
R_0(2^{R_1(1)})
\ge
R_0(2^5)
=
R_0(32)
=
65.
\]

Thus

\[
R_2(1)\ge 65\ge 16=A(1,4).
\]

##### Case 3: \(Q=1\), \(z\ge 2\)

By Lemma 3.1 with \(t=0\),

\[
R_{z+1}(1)
\ge
R_z(2^{R_{z+1}(0)}).
\]

By Lemma 3.0A,

\[
R_{z+1}(0)\ge R_0(0)=1.
\]

Hence

\[
R_{z+1}(1)\ge R_z(2).
\]

Now apply Lemma 3.2 with level \(z-1\) and \(Q=2\):

\[
R_z(2)\ge R_{z-1}(8).
\]

Because \(z-1\ge 1\), Lemma 3.3 gives

\[
R_{z-1}(8)\ge A(z,8).
\]

By monotonicity of \(A(z,-)\) from Lemma 3.2A,

\[
A(z,8)\ge A(z,4).
\]

Therefore

\[
R_{z+1}(1)\ge A(z,4).
\]

This is exactly the desired statement when \(Q=1\).

Combining all cases proves

\[
R_{z+1}(Q)\ge A(z,4Q)
\]

for every \(z\ge 1\), \(Q\ge 1\).

Finally, if

\[
A(z,4Q)>r,
\]

then, since \(r\) is an integer,

\[
r\le A(z,4Q)-1\le R_{z+1}(Q).
\]

Thus

\[
J_{z+1}(r)\le Q.
\]

This proves the equivalent forward form.

## 4. Normalization consequence

This section translates the closed comparison theorem into the packet’s patched and source-faithful inverse thresholds.

### 4.1 Patched integer threshold

Define

\[
\alpha_J^Q(m,n)
=
\min\{k\ge 0:J_k(L(n))\le Q(m,n)\},
\]

where

\[
L(n)=\lceil \log_2 \max(n,2)\rceil,
\qquad
Q(m,n)=\left\lceil 1+\frac mn\right\rceil.
\]

Define

\[
\alpha_Q(m,n)
=
\min\{z\ge 1:A(z,4Q(m,n))>L(n)\}.
\]

#### Theorem 4.1

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

By definition of \(\alpha_Q\),

\[
A(z,4Q)>L.
\]

By Theorem 3.4,

\[
R_{z+1}(Q)\ge A(z,4Q)>L.
\]

Since \(L\) is an integer,

\[
L\le R_{z+1}(Q).
\]

By definition of \(R_{z+1}(Q)\),

\[
J_{z+1}(L)\le Q.
\]

Therefore

\[
\alpha_J^Q(m,n)\le z+1=\alpha_Q(m,n)+1.
\]

This proves the theorem.

---

### 4.2 Source-faithful real threshold

The current packet’s source anchor records the inverse threshold as

\[
J_k(\lceil \log_2 n\rceil)\le 1+\frac mn.
\]

With the packet cutoff \(L(n)=\lceil \log_2\max(n,2)\rceil\), define

\[
\alpha_J^S(m,n)
=
\min\left\{k\ge 0:J_k(L(n))\le 1+\frac mn\right\}.
\]

#### Lemma 4.2: Ackermann buffer

For every \(z\ge 1\) and every integer \(p\ge 1\),

\[
A(z+1,4p)\ge A(z,4p+4).
\]

#### Proof

First, \(A(i,x)\) is nondecreasing in \(x\) for every \(i\ge 0\). This follows by induction on \(i\) from the recursion

\[
A(i,x+1)=A(i-1,A(i,x)).
\]

Second, for every \(i\ge 1\) and \(x\ge 1\),

\[
A(i,x)\ge 2x.
\]

Indeed, \(A(i,1)=2\). For \(x\ge 2\), using the recursion and induction in \(x\),

\[
A(i,x)
=
A(i-1,A(i,x-1))
\ge
2A(i,x-1)
\ge
4(x-1)
\ge
2x.
\]

Now fix \(z\ge 1\), \(p\ge 1\). Since \(4p\ge 2\),

\[
A(z+1,4p)
=
A\bigl(z,A(z+1,4p-1)\bigr).
\]

We claim

\[
A(z+1,4p-1)\ge 4p+4.
\]

If \(p=1\), then \(4p-1=3\). Also \(A(i,2)=4\) for every \(i\ge 1\), because

\[
A(i,2)=A(i-1,A(i,1))=A(i-1,2),
\]

and this descends to \(A(1,2)=4\). Hence

\[
A(z+1,3)=A(z,A(z+1,2))=A(z,4)\ge 8=4p+4.
\]

If \(p\ge 2\), then

\[
A(z+1,4p-1)\ge 2(4p-1)=8p-2\ge 4p+4.
\]

Thus in all cases,

\[
A(z+1,4p-1)\ge 4p+4.
\]

By monotonicity of \(A(z,-)\),

\[
A(z+1,4p)
=
A\bigl(z,A(z+1,4p-1)\bigr)
\ge
A(z,4p+4).
\]

This proves the lemma.

#### Theorem 4.3

For all positive integers \(m,n\),

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+2.
\]

If \(1+m/n\) is integral, then the sharper bound holds:

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

By definition,

\[
A(z,4Q)>L.
\]

##### Integral case

If \(s\) is an integer, then \(Q=s\). By Theorem 3.4,

\[
R_{z+1}(s)
=
R_{z+1}(Q)
\ge
A(z,4Q)
>
L.
\]

Since \(L\) is an integer,

\[
L\le R_{z+1}(s).
\]

Therefore

\[
J_{z+1}(L)\le s=1+\frac mn.
\]

Hence

\[
\alpha_J^S(m,n)\le z+1=\alpha_Q(m,n)+1.
\]

##### Nonintegral case

Assume \(s\) is not an integer. Let

\[
p=\lfloor s\rfloor.
\]

Since \(m,n\ge 1\), we have \(s>1\), so \(p\ge 1\). Also,

\[
Q=\lceil s\rceil=p+1.
\]

Thus

\[
4Q=4p+4.
\]

By definition of \(z=\alpha_Q(m,n)\),

\[
A(z,4p+4)>L.
\]

By Lemma 4.2,

\[
A(z+1,4p)\ge A(z,4p+4)>L.
\]

Apply Theorem 3.4 with level parameter \(z+1\) and threshold \(p\):

\[
R_{z+2}(p)\ge A(z+1,4p)>L.
\]

Since \(L\) is an integer,

\[
L\le R_{z+2}(p),
\]

and therefore

\[
J_{z+2}(L)\le p.
\]

Because

\[
p=\lfloor s\rfloor<s=1+\frac mn,
\]

we get

\[
J_{z+2}(L)\le 1+\frac mn.
\]

Thus

\[
\alpha_J^S(m,n)
\le
z+2
=
\alpha_Q(m,n)+2.
\]

This proves the theorem.

---

### 4.3 Cost consequence

#### Theorem 4.4

Using the packet recurrence bound

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

By Theorem 4.1,

\[
J_{z+1}(L)\le Q.
\]

Apply the packet recurrence bound with \(r=L\) and \(k=z+1\):

\[
f(m,n,L)
\le
(z+1)m+2nJ_{z+1}(L)
\le
(z+1)m+2nQ.
\]

Now

\[
Q
=
\left\lceil 1+\frac mn\right\rceil
\le
2+\frac mn.
\]

Therefore

\[
2nQ
\le
2n\left(2+\frac mn\right)
=
4n+2m.
\]

Hence

\[
f(m,n,L)
\le
(z+1)m+4n+2m
=
(z+3)m+4n.
\]

Substituting \(z=\alpha_Q(m,n)\) gives

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n.
\]

The asymptotic bound

\[
f(m,n,L(n))=O(m\alpha_Q(m,n)+n)
\]

follows immediately.

---

### 4.4 Caveat: the alternate \(2m/n\) threshold

The current packet’s source anchor records the source-faithful threshold as

\[
J_k(\lceil \log_2 n\rceil)\le 1+\frac mn.
\]

Therefore

\[
J_k(\lg n)\le \frac{2m}{n}
\]

should not be cited as source-faithful under the current packet unless independently verified from the paper. Under the packet, it is only an alternate stricter threshold.

There is also a direct obstruction in the low-load range.

#### Lemma 4.5

For every \(k\ge 0\) and every integer \(r\ge 2\),

\[
J_k(r)\ge 1.
\]

#### Proof

For \(k=0\),

\[
J_0(r)=\left\lceil \frac{r-1}{2}\right\rceil.
\]

If \(r\ge 2\), then \((r-1)/2>0\), so

\[
J_0(r)\ge 1.
\]

Now assume \(J_k(r)\ge 1\) for every \(r\ge 2\). We prove the same statement for

\[
J_{k+1}=J_k^\diamond.
\]

Let \(r\ge 2\), and set \(g=J_k\). By the induction hypothesis,

\[
g(r)=J_k(r)\ge 1.
\]

The packet definition gives

\[
g^\diamond(r)=
\begin{cases}
g(r),& g(r)\le 1,\\[4pt]
1+g^\diamond(\lceil \log_2 g(r)\rceil),& g(r)>1.
\end{cases}
\]

If \(g(r)\le 1\), then \(g(r)=1\), so

\[
J_{k+1}(r)=g^\diamond(r)=1.
\]

If \(g(r)>1\), then

\[
J_{k+1}(r)
=
g^\diamond(r)
=
1+g^\diamond(\lceil \log_2 g(r)\rceil)
\ge 1.
\]

Thus \(J_{k+1}(r)\ge 1\) for every \(r\ge 2\). By induction on \(k\), the lemma follows.

#### Corollary 4.6

If

\[
\frac mn<\frac12
\]

and

\[
n\ge 3,
\]

then the alternate threshold

\[
J_k(L(n))\le \frac{2m}{n}
\]

is impossible for every finite \(k\).

#### Proof

Under the packet convention,

\[
L(n)=\lceil \log_2 \max(n,2)\rceil.
\]

The condition \(n\ge 3\) is equivalent to

\[
L(n)\ge 2.
\]

If \(m/n<1/2\), then

\[
\frac{2m}{n}<1.
\]

If one demanded

\[
J_k(L(n))\le \frac{2m}{n},
\]

then since \(J_k(L(n))\) is a nonnegative integer and \(2m/n<1\), this would force

\[
J_k(L(n))=0.
\]

But \(L(n)\ge 2\), so Lemma 4.5 gives

\[
J_k(L(n))\ge 1
\]

for every \(k\). This is impossible.

Therefore the \(2m/n\) threshold cannot be silently substituted for the packet’s source-faithful threshold \(1+m/n\).

---

## 5. Dependency map

The proof chain is:

\[
\text{source definitions}
\]

\[
\Downarrow
\]

\[
J_0(r)=\left\lceil \frac{r-1}{2}\right\rceil,
\qquad
J_{k+1}=J_k^\diamond,
\qquad
f(m,n,r)\le km+2nJ_k(r)
\]

\[
\Downarrow
\]

\[
\text{threshold inverse }R_k(t)=\max\{r:J_k(r)\le t\}
\]

\[
\Downarrow
\]

\[
R_{z+1}(Q)\ge A(z,4Q)
\qquad
(c=1,\ C=1,\ D=4)
\]

\[
\Downarrow
\]

\[
\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1
\]

\[
\Downarrow
\]

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n
=
O(m\alpha_Q(m,n)+n).
\]

The source-faithful real threshold

\[
J_k(L(n))\le 1+\frac mn
\]

is handled by the additional integer/real threshold conversion:

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+2,
\]

with a \(+1\) improvement when \(1+m/n\) is integral.

---

## 6. Audit checklist

### Does the note prove the exact coordinator target?

Yes. The coordinator target asks for constants \(c,C,D\) such that

\[
R_{cz+C}(Q)\ge A(z,DQ).
\]

The note proves

\[
R_{z+1}(Q)\ge A(z,4Q)
\]

for all \(z\ge 1\), \(Q\ge 1\). Thus

\[
c=1,\qquad C=1,\qquad D=4.
\]

### Does it avoid generic union-find/Tarjan-potential drift?

Yes. The proof stays inside the top-down `J` hierarchy, the `g^\diamond` recurrence, the threshold inverse \(R_k\), and the packet recurrence bound

\[
f(m,n,r)\le km+2nJ_k(r).
\]

It does not use bottom-up Tarjan potentials, lower bounds, implementation arguments, or a general union-find proof.

### Are constants \(c,C,D\) explicit?

Yes:

\[
c=1,\qquad C=1,\qquad D=4.
\]

### Are \(L(n)\) and \(Q(m,n)\) patched exactly?

Yes. The note uses

\[
L(n)=\lceil \log_2\max(n,2)\rceil
\]

and

\[
Q(m,n)=\left\lceil 1+\frac mn\right\rceil.
\]

### Is the source threshold \(1+m/n\) distinguished from alternate \(2m/n\)?

Yes. The source-faithful threshold under the current packet is

\[
J_k(\lceil \log_2 n\rceil)\le 1+\frac mn.
\]

The threshold

\[
J_k(\lg n)\le \frac{2m}{n}
\]

is explicitly marked as non-source-faithful under the current packet unless independently rechecked.

### Are all additive shifts named?

Yes.

The patched integer threshold gives

\[
\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1.
\]

The exact source-faithful real threshold gives

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+2.
\]

When \(1+m/n\) is integral, the source threshold improves to

\[
\alpha_J^S(m,n)\le \alpha_Q(m,n)+1.
\]

The cost bound has the additive constants

\[
f(m,n,L(n))
\le
(\alpha_Q(m,n)+3)m+4n.
\]

### Are any claims conditional on source anchors or earlier source-fidelity?

Yes. The following are packet/source-anchor dependent:

1. The source threshold being

   \[
   J_k(\lceil \log_2 n\rceil)\le 1+\frac mn.
   \]

2. The packet rank cutoff

   \[
   L(n)=\lceil \log_2\max(n,2)\rceil.
   \]

3. The recurrence consequence

   \[
   f(m,n,r)\le km+2nJ_k(r).
   \]

4. The rejection of \(2m/n\) as source-faithful under the current packet. That threshold should not be cited as source-faithful unless independently verified from the original paper.

---

## 7. Final safely citable theorem block

```text
Final theorem block: top-down J hierarchy implies the packet-normalized inverse-Ackermann bound.

Assume the packet definitions

    J_0(r) = ceil((r-1)/2),
    J_{k+1} = J_k^diamond,

where

    g^diamond(r) = g(r)                                      if g(r) <= 1,
    g^diamond(r) = 1 + g^diamond(ceil(log_2 g(r)))            if g(r) > 1.

Define

    R_k(t) = max { r >= 0 : J_k(r) <= t }.

Under the packet convention, this is a finite threshold inverse of J_k.

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

Using the packet recurrence bound

    f(m,n,r) <= k m + 2n J_k(r),

this gives

    f(m,n,L(n)) <= (alpha_Q(m,n)+3)m + 4n,

and hence

    f(m,n,L(n)) = O(m alpha_Q(m,n) + n).

For the current packet's source-faithful threshold

    J_k(L(n)) <= 1 + m/n,

define

    alpha_J^S(m,n)
      = min { k >= 0 : J_k(L(n)) <= 1 + m/n }.

Then

    alpha_J^S(m,n) <= alpha_Q(m,n)+2.

If 1 + m/n is integral, then the sharper bound holds:

    alpha_J^S(m,n) <= alpha_Q(m,n)+1.

The alternate threshold J_k(lg n) <= 2m/n is not source-faithful under the current packet unless independently verified from the paper. Under the packet definitions it is impossible when m/n < 1/2 and n >= 3, since then it would force J_k(L(n))=0 while J_k(r)>=1 for every k and every r>=2.
```

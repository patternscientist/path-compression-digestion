# Abstract

This note gives a source-faithful, proof-digested presentation of how the Seidel--Sharir top-down path-compression \(J\) hierarchy yields an inverse-Ackermann bound under an explicit classical Ackermann normalization. The central comparison is phrased through the threshold inverse
\[
R_k(t)=\max\{r\ge 0:J_k(r)\le t\},
\]
and proves
\[
R_{z+1}(Q)\ge A(z,4Q)
\]
for all \(z\ge 1\) and \(Q\ge 1\), with constants \(c=1\), \(C=1\), and \(D=4\) in the coordinator target \(R_{cz+C}(Q)\ge A(z,DQ)\). The proof stays entirely within the top-down \(J\)-hierarchy and its \(g^\diamond\) recurrence, avoiding bottom-up Tarjan-potential arguments. It then translates the comparison into the packet-normalized thresholds \(L(n)=\lceil\log_2\max(n,2)\rceil\) and \(Q(m,n)=\lceil1+m/n\rceil\), giving \(\alpha_J^Q(m,n)\le \alpha_Q(m,n)+1\) and the source-faithful real-threshold bound \(\alpha_J^S(m,n)\le \alpha_Q(m,n)+2\), with a \(+1\) improvement when \(1+m/n\) is integral. Finally, using the source recurrence \(f(m,n,r)\le km+2nJ_k(r)\), it obtains \(f(m,n,L(n))\le(\alpha_Q(m,n)+3)m+4n\). The note also documents source anchors, normalization choices, and hazards avoided.

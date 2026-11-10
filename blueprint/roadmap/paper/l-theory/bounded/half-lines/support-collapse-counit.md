---
article_id: af_f822f63c5158a713678cb073
declaration: def
origin: background
---

# Collapse counit

The *collapse counit* is the natural isomorphism $\varepsilon:\iota_0\circ\sigma\cong\mathrm{id}_{H_b}$ whose component at $M\in H_b$ is the matrix $\varepsilon_M:\iota_0\sigma M\to M$ with $(n,0)$ entry the projection $\bigoplus_{|k|\le\rho(M)}M_k\to M_n$ for $|n|\le\rho(M)$ and all other entries zero, and whose inverse component is the matrix of inclusions $M_n\to\bigoplus_kM_k$ in the entries $(0,n)$.

*Proof sketch.* (Proof obligations.) Both matrices have propagation at most $\rho(M)$, since their nonzero entries sit at $(n,0)$ and $(0,n)$ with $|n|\le\rho(M)$, so they are morphisms. The two composites are $\sum_n\iota_n\pi_n=1$ on $\sigma M$ in degree $0$ and $\pi_n\iota_m=\delta_{nm}$ on $M$; the entries outside the windows are maps out of zero objects. Naturality in $f:M\to N$: both $f\varepsilon_M$ and $\varepsilon_N\iota_0\sigma(f)$ have $(m,0)$ entry $\sum_nf_{mn}\pi_n$, because the entries of $N$ and $M$ outside their windows are zero objects.

## Sources

- [Ranicki 1992, §16](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Degree-zero inclusion](degree-zero-inclusion.md)
- [Support collapse](support-collapse.md)

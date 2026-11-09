---
article_id: af_f822f63c5158a713678cb073
declaration: def
origin: background
---

# Collapse counit

For $M\in H_b$, let $\varepsilon_M:\iota_0\sigma M\to M$ be the matrix whose $(n,0)$ entry is the projection $\bigoplus_{|k|\le\rho(M)}M_k\to M_n$ for $|n|\le\rho(M)$, all other entries being zero. Then $\varepsilon_M$ has propagation $\rho(M)$, its inverse is the matrix of inclusions $M_n\to\bigoplus_kM_k$ in the entries $(0,n)$, and $\varepsilon:\iota_0\circ\sigma\cong\mathrm{id}_{H_b}$ is a natural isomorphism.

*Proof sketch.* The two composites are $\sum_n\iota_n\pi_n=1$ on $\sigma M$ in degree $0$ and $\pi_n\iota_m=\delta_{nm}$ on $M$; the entries outside the windows are maps out of zero objects. Naturality in $f:M\to N$: both $f\varepsilon_M$ and $\varepsilon_N\iota_0\sigma(f)$ have $(m,0)$ entry $\sum_nf_{mn}\pi_n$, because the entries of $N$ and $M$ outside their windows are zero objects.

## Sources

- [Ranicki 1992, §16](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Degree-zero inclusion](degree-zero-inclusion.md)
- [Support collapse](support-collapse.md)

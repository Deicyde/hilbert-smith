---
article_id: af_8dbbc98448ade357a521d096
declaration: lemma
origin: bridged
---

# Sheet translation

If $u$ has graph type $\chi_i(g)$ with bound $\delta$, then $\operatorname{Ind}_g u$ is $G_i$-equivariant and has propagation at most $\delta$.

*Proof sketch.* An entry $b\otimes s\to b'\otimes sg^{-1}$ joins $(\chi(s)t_b,z_b)$ to $(\chi(s)\chi(g)^{-1}t_{b'},z_{b'})$. Their distance is $\max(d(t_{b'},\chi(g)t_b),d(z_{b'},z_b))$ because $\chi(s)$ is an isometry. Right shifts commute with left multiplication.

## Sources

- HS paper, Section 10 (detector cancellation).
- New: only isometry of the $C_p$-action is used, so the computation holds over any isometric $C_p$-space.

## Depends on

- [Sheet shift](sheet-shift.md)
- [Graph-type matrices](graph-type.md)

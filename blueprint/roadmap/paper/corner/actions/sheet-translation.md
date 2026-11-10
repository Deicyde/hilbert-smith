---
article_id: af_8dbbc98448ade357a521d096
declaration: lemma
origin: bridged
---

# Sheet translation

If $u$ has graph type $\chi_i(g)$ with bound $\delta$, then $\operatorname{Ind}_g u$ is $G_i$-equivariant and has propagation at most $\delta$.

*Proof sketch.* An entry $b\otimes s\to b'\otimes(s-g)$ joins $(\chi(s)\cdot t_b,z_b)$ to $((\chi(s)-\chi(g))\cdot t_{b'},z_{b'})$. Their distance is $\max(d_T(t_{b'},\chi(g)\cdot t_b),d_S(z_{b'},z_b))$, because $\chi(s)-\chi(g)$ acts isometrically. Shifts by $-g$ commute with the action of $G_i$ on sheets.

## Sources

- HS paper, Section 10 (detector cancellation).
- New: only isometry of the $C_p$-action is used, so the computation holds over any isometric $C_p$-space.

## Depends on

- [Sheet shift](sheet-shift.md)
- [Graph-type matrices](graph-type.md)

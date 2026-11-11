---
article_id: af_d7579c14213a35f0a713484c
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.dist_F₀_le
---

# The averaged map moves points little

For a local datum with constants $(D,\rho_+)$, $|F_0(x)-x|\le D$ for all $x\in\Omega$.

*Proof sketch.* $F_0(x)-x=\int(a\cdot x-x)\,d\mu(a)$, whose norm is at most $D\cdot\mu(\mathbb Z_p)=D$ by the displacement condition.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the bound there is $2D$; here the displacement condition already holds on all of $\Omega$)

## Depends on

- [The averaged chart map](averaged-map.md)

## Proof depends on

- [The Haar probability measure on $\mathbb Z_p$](../subgroups/haar-zp.md)

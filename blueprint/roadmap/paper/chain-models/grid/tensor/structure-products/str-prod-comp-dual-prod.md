---
article_id: af_ed48685d0205371f2a12da85
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedStrProd_comp_basedDualProd
---

# A product of duality maps after a product of structures

Let $C$ and $E$ be complexes of based vector spaces vanishing in negative degrees, $\varphi\in M(C)_m$, $\theta\in M(E)_{m'}$, and $f_r:C_r\to C^*_{m-r}$, $g_r:E_r\to E^*_{m'-r}$ graded maps, $k=m+m'$. Then the [product of duality maps](based-dual-prod.md) and the [product of structures](based-str-prod.md) satisfy, in each degree $r$,
$$\Xi^{-1}(f\otimes g)_r\circ(\varphi\otimes\theta)_{r,k-r}=\Xi^{-1}\bigl((f\varphi)\otimes(g\theta)\bigr)\Xi,$$
the [dual tensor](../based-dual-tensor-hom.md) of the maps $f_t\varphi_{t,m-t}$ of $C^{m-*}$ and $g_t\theta_{t,m'-t}$ of $E^{m'-*}$ of degree $0$.

*Proof sketch.* Compare blocks from the dual of the summand $a$ to the dual of the summand $p$ of degree $k-r$. The only intermediate summand is $m-a$, and then $p=a$; the two signs $(-1)^{(r-m+a)(2m-a)}$ cancel, the sign of the dual tensor is even for $d=e=0$, and the Kronecker products combine ([Kronecker product of identities](../kron-transport.md)). If $m-a<0$ then $C_{m-a}=0$, and if $m-a>r$ then $E_{r-m+a}=0$, so both sides vanish. The right side is computed by the [blocks of a dual tensor](dual-tensor-hom-blocks.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)
- [Product of duality maps in explicit bases](based-dual-prod.md)
- [Dual tensor of graded maps of based complexes](../based-dual-tensor-hom.md)

## Proof depends on

- [Maps between concatenations are determined by their blocks](../block-ext.md)
- [Blocks of a composite](../block-comp.md)
- [Blocks of a product of structures](str-prod-blocks.md)
- [Blocks of a product of duality maps](dual-prod-blocks.md)
- [Kronecker product of composites](../kron-composite.md)
- [Kronecker product with a zero factor](../kron-zero.md)
- [Composites through a zero space vanish](zero-dim-comp.md)
- [Blocks of a dual tensor of graded maps](dual-tensor-hom-blocks.md)
- [Kronecker product of identities](../kron-transport.md)

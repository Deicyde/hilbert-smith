---
declaration: def
origin: bridged
---
# Inner cut

Let $A,B,Z\subseteq X$ be closed invariant, $S=A\cup B$, $Y=A\cap B$ and $Z\subseteq A$. The *inner cut* $\partial^{\rm in}_{A,B}:\mathbb L_k(\mathcal A_S/\mathcal A_Z)\to\mathbb L_{k-1}(\mathcal A_Y)$ is the composite of three maps:
- the map induced by the functor $\mathcal A_S/\mathcal A_Z\to\mathcal A_S/\mathcal A_A$ that is the identity on objects;
- $(e_*)^{-1}$, where $e:\mathcal A_B/\mathcal A_Y\to\mathcal A_S/\mathcal A_A$ is the [excision](../categories/excision.md) functor;
- the [boundary](../l-theory/D3.md) of $\mathcal A_Y\subseteq\mathcal A_B$.

For a class in $\mathbb L_k(\mathcal A_S)$, apply it after the quotient by $\mathcal A_\varnothing$.

## Sources
- HS paper, Section 6. New: the quotient kills the side that contains the exterior, so no separation hypothesis is needed.
## Depends on
- [Excision](../categories/excision.md), [support filtration](../categories/support-filtration.md), [boundary on 𝕃](../l-theory/D3.md), [functoriality](../l-theory/D2.md)

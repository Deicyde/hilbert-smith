---
article_id: af_cada4605f6cb5069560d3d7c
declaration: theorem
origin: bridged
---
# Block duality

For every block $Q$:
1. $T\varphi_Q=\varphi_Q$, $T\varphi_{\partial Q}=\varphi_{\partial Q}$, $d\varphi_{\partial Q}=\varphi_{\partial Q}\delta$, and $d\varphi_Q-\varphi_Q\delta=j\varphi_{\partial Q}j^*$;
2. the restriction $\Psi_Q$ of $\varphi_Q$ to $(Q/\partial Q)^{N_Q-*}$ is a chain map to $Q$, with homotopy inverse $b_Q$ and explicit homotopies;
3. every map in (1)-(2) moves each coordinate by at most that factor's mesh, so its $d_\infty$-propagation is at most the largest mesh;
4. $dz_Q=jz_{\partial Q}$ for a cycle $z_{\partial Q}$, and $\varepsilon\Psi_Q(\alpha)=\alpha(z_Q)$ for $\alpha$ of degree $0$.

*Proof sketch.* Tensor the [circle](../grid/circle-duality.md) and [arc](arc-duality.md) identities [U]. The Leibniz rule turns the arc defects into $j\varphi_{\partial Q}j^*$. Relative cochains of a product are the tensor product of the relative cochains of the factors. Telescope the homotopies as in the [Poincaré](../grid/chain-model-poincare.md) theorem.

## Sources
- [Ranicki 1980, products of pairs](../../../../sources/paper/ranicki-1980.md) [U]; HS paper, Section 12 (relative duality, cylinders). New: exact tensor formulas.
## Depends on
- [Block pair](block-pair.md), [strict pair](../../l-theory/base/pairs/poincare-pair.md)
## Proof depends on
- [Circle duality](../grid/circle-duality.md), [arc duality](arc-duality.md)

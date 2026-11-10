---
article_id: af_2f0a4e4dd70126cf111cbb76
declaration: lemma
origin: cited
---

# $L^p$ of a half-line vanishes

$L^p_m(H_\varepsilon)=0$ for all $m$.

*Proof sketch.* (1) The shift $\Sigma^\varepsilon$, $(\Sigma^\varepsilon M)_n=M_{n-\varepsilon}$, is a strict duality functor of $H_\varepsilon$. The identity matrices form a natural isomorphism $M\to\Sigma^\varepsilon M$ of propagation $1$, which is unitary because its dual is again the identity matrix. So $\Sigma^\varepsilon_*=\mathrm{id}$ on $L^p_m(H_\varepsilon)$ by [Functoriality on L^p](../../base/groups/lp-functoriality.md) (unitary invariance and the identity). (2) For a strict Poincaré complex $(C,\phi)$ in $\mathrm{Kar}\,H_\varepsilon$, put $G=\bigoplus_{k\ge0}\Sigma^{\varepsilon k}C$ with the sum structure. Each degree of each chain object is a finite sum, because the supports move away from $-\infty$ in the direction $\varepsilon$, and the sums of the inverses and homotopies keep a uniform propagation. So $(G,\phi_G)$ is a strict Poincaré complex in $\mathrm{Kar}\,H_\varepsilon$. (3) The evident isomorphism $G\cong C\oplus\Sigma^\varepsilon G$ carries structures exactly, so [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) and [Group structure on L](../../base/groups/l-group-add.md) give $[G]=[C]+\Sigma^\varepsilon_*[G]=[C]+[G]$. Hence $[C]=0$.

## Sources

- [Ranicki 1992, §16](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [L-group](../../base/groups/l-group.md)
- [Half-line subcategories](half-lines.md)

## Proof depends on

- [Functoriality on L^p](../../base/groups/lp-functoriality.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Group structure on L](../../base/groups/l-group-add.md)

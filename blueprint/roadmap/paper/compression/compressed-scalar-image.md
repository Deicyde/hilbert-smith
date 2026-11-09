---
declaration: lemma
origin: bridged
---
# Scalar image of the compressed complex

Let $U':\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ push labels forward along the projection. With $\mathbf k$ the [mesh sequence](../chain-models/mesh-sequence.md),
$$U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{\mathbf k}(f_T).$$

*Proof sketch.* $U'_*\operatorname{cls}=\operatorname{cls}(U'C,\hat\varphi)$ by functoriality. Let $D'$ equal $D_i$ for $i\ge i_0$ and $0$ before. It is unitarily isomorphic to $D$, because the two agree eventually. With the labels $s_b=f_T(x_b)$, $\mathrm{pr}:D'\to U'C$ and $\mathrm{in}$ have propagation $0$. Moreover $\mathrm{pr}$ is an exact chain map with $\mathrm{pr}\,\mathrm{in}=1$. The map $Q$ factors through the discarded cells, whose labels have $|s_b|>t>R$, so $Q=0$ in $\mathcal B_{\mathbf 1,Z_0}$. Hence $\mathrm{pr}$ is an isomorphism there, and $\mathrm{pr}\,\varphi\,\mathrm{pr}^*=\hat\varphi$. Apply homotopy-isometry invariance.

## Sources
- HS paper, Section 10 (after forgetting $T$).
## Depends on
- [Compressed Poincaré](compressed-poincare.md), [labelled model class](labelled-model-class.md), [pushforward](../categories/pushforward.md), [support preservation](../categories/support-preservation.md)
## Proof depends on
- [Functoriality](../l-theory/D2.md), [homotopy-isometry invariance](../l-theory/A9.md), [relabelling isomorphism](../categories/relabelling-isomorphism.md), [discarded subcomplex](discarded-subcomplex.md)

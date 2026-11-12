---
article_id: af_90a5b0f9a0f674bee9fee189
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.ChainModels.isometry_homotopies
---
# Isometry homotopies

Put $s_i=3\omega(2h_i)+8h_i$, with $\omega$ the [modulus](modulus.md). For $g\in G_i$ there are $U^T_g\in M(C(k_i))_{n+1}$ such that $U_g=U^T_g\otimes\varphi_P\in M(D_i)_{N+1}$ (the external product of [chain-model duality](../grid/chain-model-duality.md) (1)) satisfies
$$a_g\varphi_ia_g^*-\varphi_i=dU_g+U_gd,$$
with $d$ the differentials of $D_i$ and $D_i^{N-*}$, and $U_g$ has $d_\infty$-propagation at most $s_i+2h_i$ in torus labels.

*Proof sketch.* Let $\varphi_C=\varphi^s\otimes\dots\otimes\varphi^s\in M(C(k_i))_n$, so that $\varphi_i=\varphi_C\otimes\varphi_P$. Write $a_g=a^T\otimes1_P$ ([carried group approximations](group-approx-carried.md)). On $C^{n-*}$, with $C=C(k_i)$, take $\Gamma(c^*)=\mathrm{Box}(N_{s_i}(\operatorname{st}c))$. It is nested under the differential of $C^{n-*}$, because that differential sends $c^*$ to duals of cofaces $e\supseteq c$, and $\operatorname{st}e\subseteq\operatorname{st}c$. Both $a^T\varphi_C(a^T)^*$ and $\varphi_C$ are carried: with $\hat g=\widehat{r_i(g)}$, an entry of $(a^T)^*$ at $c^*$ picks $e$ with $c\in\Gamma_{\hat g}(e)$, $\varphi_C(e^*)$ lies in cells of $\operatorname{st}e$, and $a^T$ lands within $s_i$ of $|c|$. In degree $0$, $\varepsilon a^T\varphi_C(a^T)^*(\alpha)=\alpha(a^Tz(k_i))=\alpha(z(k_i))=\varepsilon\varphi_C(\alpha)$, by the argument of [Poincaré](../grid/chain-model-poincare.md) (4) and the [fundamental cycle](fundamental-cycle-fixed.md). [Carried homotopies](../grid/carried-homotopy.md) give $U^T_g$ with $a^T\varphi_C(a^T)^*-\varphi_C=\partial U^T_g$ and the propagation bound. Then [pushforward of products](../../l-theory/localization/products/product-push.md) gives $a_g\varphi_ia_g^*=(a^T\varphi_C(a^T)^*)\otimes\varphi_P$, and the [Leibniz rule](../../l-theory/localization/products/product-leibniz.md) with $\partial\varphi_P=0$ gives $\partial U_g=\partial U^T_g\otimes\varphi_P$. Finally $\partial U=dU+Ud$ in this notation.

## Sources
- HS paper, Section 9.
## Depends on
- [Torus labels of chain-model cells](../grid/model/chain-model-label.md)
- [The cellular chain complex of CP^2](../grid/cp2/cp2-complex.md)
- [The structure of CP^2](../grid/cp2/cp2-structure.md)
- [Cubical torus grid](../grid/cubical/cubical-torus-grid.md)
- [The cells of CP^2 vanish in negative degrees](../grid/cp2/cp2-dim-neg.md)
- [Poincaré](../grid/chain-model-poincare.md), [group approximations](group-approx.md), [modulus of the track family](modulus.md), [chain-model duality](../grid/chain-model-duality.md)
## Proof depends on
- [Carried homotopies](../grid/carried-homotopy.md), [carried group approximations](group-approx-carried.md), [fundamental cycle](fundamental-cycle-fixed.md), [box hull properties](../grid/box-hull-properties.md), [pushforward of products](../../l-theory/localization/products/product-push.md), [Leibniz rule for products](../../l-theory/localization/products/product-leibniz.md)

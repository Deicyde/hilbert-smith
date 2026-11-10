---
article_id: af_a5f120c3074359723a650675
declaration: lemma
origin: bridged
---
# Residual identities

For $i\ge i_0$ and $g,h\in G_i$, with $\hat d$ the compressed differential of $C$ and of $C^{N-*}$ ([compressed maps](compressed-maps.md)), exactly:
1. $\hat d\hat A_g-\hat A_g\hat d=\mathrm{pr}\,a_gQd\,\mathrm{in}$;
2. $\hat A_g\hat A_h-\hat A_{g+h}-\hat d\hat B_{g,h}-\hat B_{g,h}\hat d=-\mathrm{pr}\,a_gQa_h\,\mathrm{in}+\mathrm{pr}\,B_{g,h}Qd\,\mathrm{in}$;
3. $\hat A_g\hat\varphi-\hat\varphi\hat A_{-g}^*-\hat d\hat V_g-\hat V_g\hat d=-\mathrm{pr}\,a_gQ\varphi_i\,\mathrm{pr}^*+\mathrm{pr}\,\varphi_iQ^*a_{-g}^*\,\mathrm{pr}^*$;
4. $\hat d\hat\varphi=\hat\varphi\hat d$, $\hat\varphi$ is fixed by the duality involution, and $\hat A_0=1$;
5. $\hat d\hat b-\hat b\hat d=-\mathrm{in}^*dQ^*b_i\,\mathrm{in}+\mathrm{in}^*b_iQd\,\mathrm{in}$;
6. $\hat\varphi\hat b-1-\hat d\hat H-\hat H\hat d=\mathrm{pr}\,H_iQd\,\mathrm{in}-\mathrm{pr}\,\varphi_iQ^*b_i\,\mathrm{in}$;
7. $\hat b\hat\varphi-1-\hat d\hat H'-\hat H'\hat d=\mathrm{in}^*dQ^*H'_i\,\mathrm{pr}^*-\mathrm{in}^*b_iQ\varphi_i\,\mathrm{pr}^*$.

Here $Q=Q_i$, and $d$ is the differential of $D_i$ or of $D_i^{N-*}$ as the source requires.

*Proof sketch.* Expand each product of compressed maps with the [product rule](compression-product-rule.md). Apply the raw identities, all written with $d$ on both $D_i$ and $D_i^{N-*}$: $a_g$, $\varphi_i$ and $b_i$ are chain maps; $a_ga_h-a_{g+h}=dB_{g,h}+B_{g,h}d$; $dV_g+V_gd=a_g\varphi_i-\varphi_ia_{-g}^*$; $\varphi_ib_i-1=dH_i+H_id$; $b_i\varphi_i-1=dH'_i+H'_id$. The words through $Q$ with $d$ on the left vanish: $\mathrm{pr}\,dQ=0$ and $Q^*d\,\mathrm{pr}^*=0$ ([discarded subcomplex](discarded-subcomplex.md); on cochains $d$ is $\pm d^*$ in each degree). The involution commutes with $\varphi\mapsto\mathrm{pr}\,\varphi\,\mathrm{pr}^*$, and $a_0=1$ gives $\hat A_0=\mathrm{pr}\,\mathrm{in}=1$.

## Sources
- HS paper, Section 10. New: the signs are rechecked, and items 5-7 are written without the HS paper's auxiliary maps.

## Depends on

- [Compressed maps](compressed-maps.md)

## Proof depends on

- [Product rule](compression-product-rule.md)
- [Discarded subcomplex](discarded-subcomplex.md)
- [The chain model is Poincaré](../chain-models/grid/chain-model-poincare.md)
- [Product homotopies](../chain-models/approximations/product-homotopies.md)
- [Adjoint homotopies](../chain-models/approximations/adjoint-homotopies.md)
- [Group approximations](../chain-models/approximations/group-approx.md)
- [Carried group approximations](../chain-models/approximations/group-approx-carried.md)
- [Chain-model estimates](../chain-models/grid/chain-model-estimates.md)

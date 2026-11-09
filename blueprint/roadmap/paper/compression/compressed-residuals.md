---
article_id: af_a5f120c3074359723a650675
declaration: lemma
origin: bridged
---
# Residual identities

For $i\ge i_0$ and $g,h\in G_i$, exactly:
1. $\hat d\hat A_g-\hat A_g\hat d=\mathrm{pr}\,a_gQd\,\mathrm{in}$;
2. $\hat A_g\hat A_h-\hat A_{g+h}-\hat d\hat B_{g,h}-\hat B_{g,h}\hat d=-\mathrm{pr}\,a_gQa_h\,\mathrm{in}+\mathrm{pr}\,B_{g,h}Qd\,\mathrm{in}$;
3. $\hat A_g\hat\varphi-\hat\varphi\hat A_{-g}^*-\hat d\hat V_g-\hat V_g\hat\delta=-\mathrm{pr}\,a_gQ\varphi_i\,\mathrm{pr}^*+\mathrm{pr}\,\varphi_iQ^*a_{-g}^*\,\mathrm{pr}^*$;
4. $\hat d\hat\varphi=\hat\varphi\hat\delta$, $T\hat\varphi=\hat\varphi$, and $\hat A_0=1$;
5. $\hat\delta\hat b-\hat b\hat d=-\mathrm{in}^*\delta Q^*b_i\,\mathrm{in}+\mathrm{in}^*b_iQd\,\mathrm{in}$;
6. $\hat\varphi\hat b-1-\hat d\hat H-\hat H\hat d=\mathrm{pr}\,H_iQd\,\mathrm{in}-\mathrm{pr}\,\varphi_iQ^*b_i\,\mathrm{in}$;
7. $\hat b\hat\varphi-1-\hat\delta\hat H'-\hat H'\hat\delta=\mathrm{in}^*\delta Q^*H'_i\,\mathrm{pr}^*-\mathrm{in}^*b_iQ\varphi_i\,\mathrm{pr}^*$.

*Proof sketch.* Expand each compressed product with the [product rule](compression-product-rule.md). Apply the raw identities: $a_g$, $\varphi_i$ and $b_i$ are chain maps; $a_ga_h-a_{g+h}=dB+Bd$; $dV_g+V_g\delta=a_g\varphi_i-\varphi_ia_{-g}^*$; $\varphi_ib_i-1=dH+Hd$; $b_i\varphi_i-1=\delta H'+H'\delta$. Use $\mathrm{pr}\,dQ=0$ and $Q^*\delta\,\mathrm{pr}^*=0$ to move $\hat d,\hat\delta$ across $\mathrm{pr},\mathrm{pr}^*$. Also $T(\mathrm{pr}\,\varphi\,\mathrm{pr}^*)=\mathrm{pr}(T\varphi)\mathrm{pr}^*$, and $a_0=1$ gives $\hat A_0=\mathrm{pr}\,\mathrm{in}=1$.

## Sources
- HS paper, Section 10; the signs are rechecked, and items 5-7 are written without $e,e^\vee$.
## Depends on
- [Compressed maps](compressed-maps.md)
## Proof depends on
- [Product rule](compression-product-rule.md), [discarded subcomplex](discarded-subcomplex.md), [Poincaré](../chain-models/grid/chain-model-poincare.md), [product homotopies](../chain-models/approximations/product-homotopies.md), [adjoint homotopies](../chain-models/approximations/adjoint-homotopies.md), [group approximations](../chain-models/approximations/group-approx.md)

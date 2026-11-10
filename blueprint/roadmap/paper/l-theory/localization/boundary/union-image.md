---
article_id: af_b607d893f03ad70249dfd905
declaration: lemma
origin: bridged
---

# The closed union becomes the image of the pair

In the setting of [Closing a pair by a null-cobordism of its boundary](closed-union.md), the projection $p:q(D\cup_PR)\to qD$ onto the first summand is an isomorphism of complexes in $\mathrm{Kar}(\mathcal A/\mathcal U)$, and $p_\%(q_\%\Phi)=q_\%\delta\phi$.

*Proof sketch.* (1) $q\circ i$ sends every object to a zero object, because an idempotent on an object of $\mathcal U$ factors through $\mathcal U$ and so is $0$ in $\mathcal A/\mathcal U$. So $qiR_{\bullet,r}$ and $qiP_{r-1}$ are zero objects, and every map into or out of them is zero. (2) The first component of the differential of $D\cup_PR=\mathcal C((f,ig))$ is $(x,z,y)\mapsto dx+(-1)^{r-1}fy$. After $q$ the term $(qf)y$ vanishes, so $p$ is a chain map. It is an isomorphism because the other two summands are zero objects. (3) The $(D_r,D^*_{k-r})$ entry of $\Phi_r$ is $\delta\phi_r$ ([Algebraic union](../../base/pairs/algebraic-union.md)), and $p$ discards the other entries, so $p_\%(q_\%\Phi)=q_\%\delta\phi$.

## Sources

- New: modulo $\mathcal U$ the pieces from $\mathrm{Kar}\,\mathcal U$ vanish degreewise, as in the HS paper, Section 6 (lines 568-571)

## Depends on

- [Closing a pair by a null-cobordism of its boundary](closed-union.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)

## Proof depends on

- [Algebraic union](../../base/pairs/algebraic-union.md)
- [Mapping cone](../../base/complexes/cone.md)

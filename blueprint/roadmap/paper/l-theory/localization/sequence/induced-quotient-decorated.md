---
article_id: af_2e5def0cc98ea604c7bd9f7a
declaration: lemma
origin: background
---

# Induced quotient functors keep decorations

In the setting of [Functor induced on quotients](induced-quotient-functor.md), $\mathrm{Kar}\,\bar F$ carries decorated objects of $\mathrm{Kar}(\mathcal A/\mathcal U)$ to decorated objects of $\mathrm{Kar}(\mathcal A'/\mathcal U')$. So the [decorated induced map](decorated-induced-map.md) $\bar F^{\mathrm{im}}_*:L^{\mathrm{im}}_k(\mathcal A/\mathcal U)\to L^{\mathrm{im}}_k(\mathcal A'/\mathcal U')$ is defined.

*Proof sketch.* Let $[M]=[qQ]$. [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md) gives $M\oplus X\cong qQ\oplus X$ for an object $X$ of $\mathcal A/\mathcal U$. Applying the additive functor $\mathrm{Kar}\,\bar F$ and $\mathrm{Kar}\,\bar F\circ\mathrm{Kar}\,q=\mathrm{Kar}\,q'\circ\mathrm{Kar}\,F$ gives $\bar FM\oplus\bar FX\cong q'(FQ)\oplus\bar FX$, with $\bar FX$ an object of $\mathcal A'/\mathcal U'$. By the same criterion, $[\bar FM]=[q'(FQ)]$.

## Sources

- New: stable equality is preserved by additive functors

## Depends on

- [Functor induced on quotients](induced-quotient-functor.md)
- [Decorated quotient L-group](decorated-l-group.md)
- [Decorated induced map](decorated-induced-map.md)

## Proof depends on

- [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md)

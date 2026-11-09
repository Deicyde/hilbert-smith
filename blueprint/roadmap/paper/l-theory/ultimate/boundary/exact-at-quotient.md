---
article_id: af_624b6de0f77d03eeef63da8a
declaration: theorem
origin: cited
---

# Ultimate exactness at the quotient

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration with quotient functor $q:\mathcal A\to\mathcal A/\mathcal U$. If $z\in\mathbb L_k(\mathcal A/\mathcal U)$ has $\partial z=0$, then $z=q_*y$ for some $y\in\mathbb L_k(\mathcal A)$.

*Proof sketch.*
1. By [Every element comes from a finite level](../groups/level-exhaustive.md), $z=\iota_jx$ with $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$. By [The ultimate boundary at each level](ultimate-boundary-level.md), $\iota_{j+1}\partial^{(j)}x=\sigma_{k,j}\partial z=0$, so [Classes zero in the colimit](../groups/level-kernel.md) gives $m$ with $t^m\partial^{(j)}x=0$.
2. Applying [Transition commutes with the boundary](../../localization/line/transition-boundary-commute.md) $m$ times, $t^m\partial^{(j)}x=\pm\partial^{(j+m)}t^mx$. Put $n=j+m+1$. So $\partial\big(t^{\mathrm{im}}t^mx\big)=0$ for the filtration $C_{\mathbb Z^n}\mathcal U\subset C_{\mathbb Z^n}\mathcal A$ ([Level boundary](../../localization/line/level-boundary.md), [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)).
3. [Exactness at the quotient](../../localization/sequence/exact-at-quotient.md) gives $y'\in L^p_{k+n}(C_{\mathbb Z^n}\mathcal A)$ with $t^{\mathrm{im}}t^mx=q_*y'$, where $q_*$ is the [quotient map](../../localization/sequence/quotient-map.md) into $L^{\mathrm{im}}_{k+n}(C_{\mathbb Z^n}\mathcal A/C_{\mathbb Z^n}\mathcal U)$.
4. Apply $e_*\circ\mathrm{forget}$, with $e$ the equivalence of [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md) and forget the map of [Forgetting the decoration](../../localization/sequence/forget-decoration.md). By [Transition and quotient](../../localization/line/transition-quotient.md), the left side becomes $t^{m+1}x$. On the right, $\mathrm{forget}\circ q_*$ is the induced homomorphism of the quotient functor $q_n:C_{\mathbb Z^n}\mathcal A\to C_{\mathbb Z^n}\mathcal A/C_{\mathbb Z^n}\mathcal U$, since both send $[C,\phi]$ to $[q_nC,(q_n)_\%\phi]$. [Functoriality of induced maps](../../base/groups/induced-map-comp.md) and $e\circ q_n=C_{\mathbb Z^n}q$ ([Transition and quotient](../../localization/line/transition-quotient.md)) give $t^{m+1}x=(C_{\mathbb Z^n}q)_*y'$.
5. By [Levels are compatible with the transition](../groups/level-compatible.md) and [The induced map at each level](../groups/induced-map-level.md), $z=\iota_nt^{m+1}x=\iota_n(C_{\mathbb Z^n}q)_*y'=q_*\iota_ny'$. Take $y=\iota_ny'$.

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level statement](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: group-level reduction to the finite level.

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Every element comes from a finite level](../groups/level-exhaustive.md)
- [The ultimate boundary at each level](ultimate-boundary-level.md)
- [Classes zero in the colimit](../groups/level-kernel.md)
- [Transition commutes with the boundary](../../localization/line/transition-boundary-commute.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
- [Exactness at the quotient](../../localization/sequence/exact-at-quotient.md)
- [Quotient map](../../localization/sequence/quotient-map.md)
- [Forgetting the decoration](../../localization/sequence/forget-decoration.md)
- [Iterated bounded quotient](../../bounded/categories/iterated-bounded-quotient.md)
- [Transition and quotient](../../localization/line/transition-quotient.md)
- [Functoriality of induced maps](../../base/groups/induced-map-comp.md)
- [Levels are compatible with the transition](../groups/level-compatible.md)
- [The induced map at each level](../groups/induced-map-level.md)
=== NOTE exact-at-quotient (ultimate)
HSP.LTheory.ult_exact_quotient. Steps 1 and 5 use `AddCommGroup.DirectLimit.induction_on`, `of.zero_exact` and `of_f`. Step 2 is an induction on m over trans_levelBoundary; only vanishing is used, so the sign is not tracked. Step 4 needs forget ∘ quotientMap = LP.map q_n, which is `rfl` if both are built from the same `Quotient.map`; otherwise it is a one-line lemma that belongs to the localization core. If transition-quotient states e ∘ q_n = C_{Z^n} q only up to unitary isomorphism, add base unitary invariance to step 4.

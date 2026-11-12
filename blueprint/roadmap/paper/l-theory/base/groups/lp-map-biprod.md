---
article_id: af_26314bf67e7428bdffca8276
declaration: theorem
origin: background
statement: formalized
lean: HSP.Lp.map_biprod
proof: formalized
---

# Sums of functors on L^p

For duality functors $F,G:\mathcal A\to\mathcal A'$ and their [sum](../categories/sums/duality-functor-sum.md) $F\oplus G$, $(F\oplus G)_*=F_*+G_*$ on $L^p_k(\mathcal A)$, where $F_*=(\mathrm{Kar}\,F)_*$ as in [Induced homomorphism](induced-map.md).

*Proof sketch.* The [completion](../categories/karoubi-functor.md) $\mathrm{Kar}(F\oplus G)$ sends $(M,e)$ to $(FM\oplus GM,Fe\oplus Ge)$. The maps $\pi_{FM}\circ(Fe\oplus Ge)$ and $\pi_{GM}\circ(Fe\oplus Ge)$ to $(FM,Fe)$ and $(GM,Ge)$ form an isomorphism $\eta_{(M,e)}$ onto the sum $(FM,Fe)\oplus(GM,Ge)$ in $\mathrm{Kar}\,\mathcal A'$, with inverse $(Fe\oplus Ge)\circ\iota_{FM}$, $(Fe\oplus Ge)\circ\iota_{GM}$ on the summands. These maps are natural in $(M,e)$. They form a [unitary natural isomorphism](../categories/unitary-isomorphism.md) $\mathrm{Kar}(F\oplus G)\cong\mathrm{Kar}\,F\oplus\mathrm{Kar}\,G$. Indeed, by the unfolding of the duality isomorphism of a sum, $\eta^*\xi^{\mathrm{Kar}F\oplus\mathrm{Kar}G}\eta$ is the sum of the $FM$ and $GM$ terms $\pi_{FM}^*\,\xi_M\,F(e^*)\,\pi_{FM}$ and $\pi_{GM}^*\,\zeta_M\,G(e^*)\,\pi_{GM}$, using $\xi_M\,F(e^*)=(Fe)^*\,\xi_M$ and that $e$ is idempotent. That sum is the duality isomorphism $\xi^{F\oplus G}_M\circ(F\oplus G)(e^*)$ of $\mathrm{Kar}(F\oplus G)$. Conclude by [unitary invariance](unitary-invariance.md) and [Sums of functors](sum-of-functors.md).

## Sources

- New: item 3 of [Functoriality on L^p](lp-functoriality.md).

## Depends on

- [Induced homomorphism](induced-map.md)
- [Sum of duality functors](../categories/sums/duality-functor-sum.md)

## Proof depends on

- [Completion of a duality functor](../categories/karoubi-functor.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)
- [Unitary invariance](unitary-invariance.md)
- [Sums of functors](sum-of-functors.md)

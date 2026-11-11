---
article_id: af_a57cafc19b6a3cfb8136f1f9
declaration: theorem
origin: background
statement: formalized
lean: HSP.Lp.map_eq_of_unitaryIso
proof: formalized
---

# Unitary invariance on L^p

If $F,G:\mathcal A\to\mathcal A'$ are duality functors and $\eta:F\cong G$ is a [unitary natural isomorphism](../categories/unitary-isomorphism.md), then $F_*=G_*$ on $L^p_k(\mathcal A)$, where $F_*=(\mathrm{Kar}\,F)_*$ as in [Induced homomorphism](induced-map.md).

*Proof sketch.* $\eta$ gives $\mathrm{Kar}\,\eta:\mathrm{Kar}\,F\cong\mathrm{Kar}\,G$ between the [completions](../categories/karoubi-functor.md), with components $\eta_MF(e):(FM,Fe)\to(GM,Ge)$ and inverses $\eta_M^{-1}G(e)$. It is natural because $\eta$ is, and unitary because $\eta$ is and $\eta_MF(e)=G(e)\eta_M$. Conclude by [unitary invariance](unitary-invariance.md).

## Sources

- New: item 2 of [Functoriality on L^p](lp-functoriality.md).

## Depends on

- [Induced homomorphism](induced-map.md)
- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)

## Proof depends on

- [Completion of a duality functor](../categories/karoubi-functor.md)
- [Unitary invariance](unitary-invariance.md)

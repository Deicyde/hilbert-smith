---
article_id: af_84d87a16eef6842e4fcd71cb
---

# Integer signatures and tails

This chapter turns ultimate $L$-classes into integers. It uses elementary linear algebra and the localization sequence from the L-theory chapter.

Write $\mathrm{Free}(\mathbb Q[G])$ for [the point category](point-functors/point-category.md) of a finite group $G$. It has three duality functors: [forgetting $G$](point-functors/forget-functor.md), [restricting to a subgroup](point-functors/restriction-functor.md), and [tensoring with a permutation module](point-functors/permutation-tensor.md). Let $b$ be a $G$-invariant nondegenerate symmetric form on a finite-dimensional real space. [Invariant definite splittings exist](l-four/signature-splitting-exists.md), and traces on the pieces define [the equivariant signature](forms/form-signature.md). [Sylvester's argument](l-four/signature-splitting-independence.md) shows that it does not depend on the splitting. The signature is [invariant under isometries](forms/form-signature-isometry.md), [additive](forms/form-signature-sum.md) and [odd](forms/form-signature-neg.md). It [vanishes when there is an invariant Lagrangian](forms/form-signature-lagrangian.md), [is multiplied by the permutation character](forms/form-signature-permutation.md), and [commutes with restriction](forms/form-signature-restrict.md). [At $g=1$ it is the integer signature](forms/form-signature-identity.md), and it obeys [the cyclotomic arithmetic](forms/form-cyclotomic.md).

[Real homology](l-four/real-homology.md) is [homotopy invariant](l-four/real-homology-invariance.md) and [dual to real cohomology](l-four/real-evaluation-pairing.md). A strict 4-dimensional Poincaré complex has a [middle form](l-four/middle-form.md), which is [nonsingular, symmetric and invariant](l-four/middle-form-nonsingular.md). Middle forms are compatible with [sums](l-four/middle-form-sum.md), [negation](l-four/middle-form-neg.md) and [permutation tensors](l-four/middle-form-permtensor.md). For a Poincaré pair, [the duality square](l-four/pair-duality-square.md) makes the image of the restriction map [a Lagrangian](l-four/pair-lagrangian.md). So [boundaries have signature zero](l-four/boundary-signature-zero.md), and the signature becomes [a homomorphism on $L^p_4$](l-four/signature-hom.md). The same goes for [the integer signature](l-four/integer-signature.md). The form rules then lift to $L^p_4$: [permutation](l-four/signature-permutation.md), [forgetting](l-four/signature-forget.md), [restriction](l-four/signature-restrict.md), [restriction of the integer signature](l-four/integer-signature-restrict.md) and [the cyclotomic rule](l-four/signature-cyclotomic.md).

The tail uses the [sequence category](point-functors/sequence-categories.md) $\mathcal P$. Its [finite-support filtration](point-functors/finite-support-filtration.md) $\mathcal S$ has the [tail category](point-functors/tail-category.md) $\mathcal V$ as quotient. Every class in $\mathbb L_4(\mathcal V)$ [lifts](tail/tail-lift.md), and [two lifts agree in almost every coordinate](tail/tail-lift-eventual.md). This defines [$\sigma_{\mathrm{tail}}$](tail/tail-signature.md) and gives [its computation rule](tail/tail-signature-lift.md). Through [the induced forgetful functor](point-functors/tail-forget-functor.md), [the tail is unchanged when $G$ is forgotten](tail/tail-signature-forget.md). Naturality of the tail under permutation tensors is handled where $\nu$ is defined, in the divisibility chapter. Downstream we only need some tail to be eventually $\pm1$, so the sign conventions of the boundary maps never matter.

## Sections

- [Point categories and their functors](point-functors/README.md)
- [Signatures of invariant forms](forms/README.md)
- [The signature on $L^p_4$](l-four/README.md)
- [The tail signature](tail/README.md)


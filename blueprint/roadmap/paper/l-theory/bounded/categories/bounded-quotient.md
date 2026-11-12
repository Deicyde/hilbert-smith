---
article_id: af_9c2350aa2a89afa35b40a51c
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: HSP.Bounded.quotientEquiv
---

# Bounded quotients

For an involution-invariant Karoubi filtration $U\subset A$, the [entrywise quotient functor](bounded-quotient-functor.md) $C_\mathbb Z(A)/C_\mathbb Z(U)\to C_\mathbb Z(A/U)$ is a duality equivalence with identity unit and counit: it has a strict duality functor inverse, and both composites are identity functors.

*Proof sketch.* (1) A bounded matrix $f$ whose entries all lie in $I_U$ factors through an object of $C_\mathbb Z(U)$. For each row $l$, the finitely many entries $f_{ln}$ inside the band all factor through one chosen decomposition $p_l$ of the target $N_l$: each entry is fixed by some chosen decomposition, and the chosen decompositions are directed ([Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)). Splitting each $p_l=i_l\rho_l$ through an object $E_l$ of $U$ gives $f=\operatorname{diag}(i_l)\circ(\operatorname{diag}(\rho_l)\circ f)$, a factorization through the object $(E_l)_l$ of $C_\mathbb Z(U)$, with [diagonal](bounded-diag.md) matrices $\operatorname{diag}(i_l)$ and $\operatorname{diag}(\rho_l)$. So two bounded matrices with the same entrywise classes have the same class modulo $C_\mathbb Z(U)$. (2) The inverse lifts every entry of a morphism of $C_\mathbb Z(A/U)$ to a representative, lifting zero entries to zero (every morphism of a [quotient by a subcategory](../../base/categories/filtration-quotient.md) is a class). The lift has the same band, and the [entrywise quotient functor](bounded-quotient-functor.md) sends it back to the original matrix. By (1) its class modulo $C_\mathbb Z(U)$ respects composition, identities, sums, scalars and transposes. With the identity duality isomorphism it is a strict duality functor. (3) Both composites are the identity on objects. On morphisms the composite starting from $C_\mathbb Z(A/U)$ returns the matrix itself; the composite starting from the quotient sends the class of $h$ to the class of a lift of the reduction of $h$, which is the class of $h$ by (1). So both composites are identity functors.

## Sources

- [Carlsson-Pedersen 1995](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Diagonal morphisms of $C_\mathbb Z(A)$](bounded-diag.md)
- [The entrywise quotient functor](bounded-quotient-functor.md)
- [The bounded subcategory is closed under sums and duals](bounded-sub-additive.md)
- [The bounded subcategory](bounded-sub.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Bounded Karoubi filtrations](bounded-karoubi-filtration.md)
- [Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [The entrywise functor](entrywise-functor.md)

## Proof depends on

- [Bounded Karoubi filtrations](bounded-karoubi-filtration.md)
- [Maps factoring through a subcategory](../../base/categories/filtration-ideal.md)

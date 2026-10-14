---
article_id: af_79b773f16b9b16082be72e1a
declaration: theorem
origin: cited
---

# Germ description

Restriction induces natural isomorphisms
$\Hom_{\Bcat(X)/\Bcat(U)}(A,B) \simeq
\colim_{N \supset X \setminus U} \Hom_{\mathsf D(N)}(A|_N, B|_N)$
for every $A, B \in \Bcat(X)$, where the colimit runs over open
neighborhoods of the complement in the ambient derived categories.
These respect composition, open restriction of duality, and
restriction of distinguished triangles. The quotient is the Verdier
quotient itself.

*Proof sketch.* Morphisms with cone in $\Bcat(U)$ become invertible
in germs, so restriction factors through the quotient. Fullness:
lift a germ representative through a cutoff supported inside its
neighborhood, giving a roof with denominator invertible near the
complement; summand sources reduce to the finite case. Faithfulness:
a morphism with zero germ vanishes in the quotient by cutting off
inside a zero neighborhood; roofs reduce to numerators. Restriction
was the functor throughout, giving the compatibilities.

## Sources

- [Preprint source map: `thm:germs`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)
- [Objects supported in an open set](compact-support.md)

## Proof depends on

- [Cutoff](cutoff.md)
- [Objects supported in an open set](compact-support.md)

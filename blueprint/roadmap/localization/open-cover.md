---
article_id: af_72f343709ca482c7ffd90a68
declaration: theorem
origin: cited
---

# Open cover dense inclusion

If $X = U \cup V$ with $U, V$ open, extension by zero induces a
fully faithful exact duality-preserving functor
$\Bcat(V)/\Bcat(U \cap V) \to \Bcat(X)/\Bcat(U)$. Its replete image
is dense: every target object is an actual summand of an object in
the image. These functors commute with $\Pcat \to \T$.

*Proof sketch.* Extension sends $\Bcat(U \cap V)$ into $\Bcat(U)$,
giving the exact functor. With $K = X \setminus U \subset V$,
neighborhoods of $K$ inside $V$ are cofinal, so the germ
description identifies both morphism groups: full faithfulness.
Density: cut off a finite object over $V$ with cone in $\Bcat(U),
so it becomes an isomorphism in the quotient with source from $V$;
summands inherit. Fullness plus exactness makes the replete image
triangulated and duality stable.

## Sources

- [Preprint source map: `prop:open-cover`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)
- [Objects supported in an open set](compact-support.md)

## Proof depends on

- [Germ description](germs.md)
- [Cutoff](cutoff.md)
- [Direct images and open extension](../sheaf-categories/test-pushforward.md)

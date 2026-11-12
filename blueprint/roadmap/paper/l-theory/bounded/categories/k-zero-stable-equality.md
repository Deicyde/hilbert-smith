---
article_id: af_1deb68c8670d900d04671d5e
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.K0.cls_eq_iff
---

# Equality in $K_0$

$[P]=[Q]$ in $K_0(\mathrm{Kar}\,A)$ iff $P\oplus M\cong Q\oplus M$ for some object $M$ of $A$.

*Proof sketch.* Grothendieck groups give $[P]=[Q]$ iff $P\oplus X\cong Q\oplus X$ for some $X=(M,e)$ in $\mathrm{Kar}\,A$. Adding the complement $(M,1-e)$ gives $X\oplus(M,1-e)\cong M$.

## Sources

- New: the Grothendieck-group criterion plus complements.

## Depends on

- [$K_0$ of an idempotent completion](k-zero.md)
- [The class of an object in $K_0$](classes/k-zero-class.md)
- [Isomorphism classes of objects](classes/iso-classes.md)

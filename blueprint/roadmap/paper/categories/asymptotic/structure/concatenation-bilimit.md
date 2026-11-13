---
article_id: af_4a26de9a5e245abb8601460a
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymCat.binaryBicone_total
---

# The concatenation is a biproduct

For the [concatenation](concatenation.md) bicone, $\mathrm{inl}\circ\mathrm{fst}+\mathrm{inr}\circ\mathrm{snd}$ is the identity of $M\oplus N$.

*Proof sketch.* This holds for the coordinate inclusions and projections of $\mathrm{Free}(\mathbb Q[G_i])$ at every level.

## Sources

- HS paper, Section 2

## Depends on

- [Concatenation](concatenation.md)
- [Asymptotic category](../asymptotic-category.md)
- [Group sequence](../group-sequence.md)

## Proof depends on

- [Free category of a finite group](../free-category.md)

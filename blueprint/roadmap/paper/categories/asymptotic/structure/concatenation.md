---
article_id: af_a90d79fc5c490cf6b295f6f6
declaration: def
origin: bridged
statement: formalized
lean: HSP.AsymCat.binaryBicone
---

# Concatenation

The concatenation of objects $M=(n_i,x_i)$ and $N=(m_i,y_i)$ of the [asymptotic category](../asymptotic-category.md) is the sequence $(n_i+m_i,x_i\sqcup y_i)$, with the inclusions $M\to M\oplus N\leftarrow N$ and projections $M\leftarrow M\oplus N\to N$ given at each level by the coordinate inclusions and projections of $\mathrm{Free}(\mathbb Q[G_i])$. They form a binary bicone; each of its four maps is the class of the sequence of these coordinate matrices.

*Proof sketch.* (Well-definedness.) The nonzero entries of the coordinate matrices join equal labels, so they have propagation $0$; the bicone identities hold levelwise.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic category](../asymptotic-category.md)
- [Free category of a finite group](../free-category.md)

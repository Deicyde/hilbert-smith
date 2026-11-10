---
article_id: af_1aa51bd59cfe5a4ff2b83857
declaration: def
origin: bridged
---

# Forgetting the group

Enumerate $G\times\{1..n\}$ by $\{1..|G|n\}$ in the fixed order used by [forgetting the group](../../categories/functors/forget-group.md). The strict duality functor $U_G:\mathrm{Free}(\mathbb Q[G])\to\mathrm{Free}(\mathbb Q)$ sends $n$ to $|G|n$ and a morphism $u:n\to n'$ to the same matrix with rows and columns reindexed along these enumerations.

*Proof sketch.* This is [reindexing](../../categories/asymptotic/free-set-basis.md) for the trivial group, whose orbit representatives are all basis elements. It preserves identities, products and transposes.

## Sources

- HS paper, Section 3
- New: in the matrix model the coefficient-of-identity trace is built in, so forgetting is a reindexing of the same matrix.

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Bases of finite free G-sets](../../categories/asymptotic/free-set-basis.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)

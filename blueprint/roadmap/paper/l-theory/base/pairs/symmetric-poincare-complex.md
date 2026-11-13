---
article_id: af_27e5e57a3ecf4de1bee54880
declaration: structure
origin: bridged
statement: formalized
lean: HSP.SymPoincare
---

# Strict symmetric Poincaré complex

A *strict $k$-dimensional symmetric Poincaré complex* in a duality category $\mathcal B$ is a pair $(C,\phi)$: a complex $C$ in $\mathcal B$ such that $C_r$ is a zero object for every $r$ outside $[0,k]$, and $\phi\in M(C)_k$ with $\partial\phi=0$ and $T\phi=\phi$, such that $\phi_\natural:C^{k-*}\to C$ is a chain homotopy equivalence.

**Remark (not formalized).** Over $\mathbb Q$, the norm $1+T:M(C)_{C_2}\to M(C)^{C_2}$ from coinvariants to invariants is an isomorphism with inverse $t\mapsto[t/2]$. So every symmetric structure has a strict representative $\phi$, with quadratic lift $\psi_0=\phi/2$. The symmetric theory therefore replaces the quadratic one.

## Sources

- HS paper, Section 5
- [Ranicki 1980 I, Prop 3.3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [The involution T](../complexes/structure-involution.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Dual complex](../complexes/dual-complex.md)
- [Structure complex](../complexes/structure-complex.md)

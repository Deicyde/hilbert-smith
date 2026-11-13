---
article_id: af_42fa0ef3cb2ac0cb1c92f974
declaration: lemma
origin: background
statement: formalized
lean: HSP.Cobordant.of_transport
proof: formalized
---

# Transported pairs are cobordisms

Let $(C,\phi)$ and $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in a duality category $\mathcal B$, $(f:E\to D,\delta\psi,\psi)$ a strict $(k+1)$-dimensional [Poincaré pair](poincare-pair.md), $u:C\oplus C'\to E$ an isomorphism, $\phi''\in M(C\oplus C')_k$ with $u_\%\phi''=\psi$, and $s=\pm1$ with $s\phi''=\phi\oplus(-\phi')$. Then $(C,\phi)$ is [cobordant](cobordism.md) to $(C',\phi')$.

*Proof sketch.* [Transport of pairs along isomorphisms](pair-transport.md) along $u$ with the sign $s$ gives a strict $(k+1)$-dimensional Poincaré pair with boundary $(C\oplus C',s\phi'')=(C\oplus C',\phi\oplus(-\phi'))$.

## Sources

- New: direct

## Depends on

- [Cobordism](cobordism.md)
- [Strict Poincaré pair](poincare-pair.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Structure complex](../complexes/structure-complex.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)

## Proof depends on

- [Transport of pairs along isomorphisms](pair-transport.md)

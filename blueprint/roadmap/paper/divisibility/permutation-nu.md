---
declaration: def
origin: bridged
---

# The endomorphism $\nu$

On the support Mayer-Vietoris functor, put $\nu_S=p\cdot\mathrm{id}-(\tau\otimes-)_*$ on $\mathbb L_k(\mathcal A_S)$. This family is a natural endomorphism.

*Proof sketch.*
1. $\tau\otimes-$ maps each $\mathcal A_S$ into itself, so it commutes strictly with the inclusions. Their induced maps commute too.
2. It carries the excisive pair $(\mathcal A_A,\mathcal A_B)$ in $\mathcal A_{A\cup B}$ into itself, so it commutes with $\partial_{A,B}$.
3. Both $p\cdot\mathrm{id}$ and $(\tau\otimes-)_*$ are additive and commute with $i$ and $\partial$, so their difference does too.

## Sources

- HS paper, Section 4.

## Depends on

- [Support Mayer-Vietoris functor](support-mayer-vietoris.md)
- [Natural endomorphism](natural-endomorphism.md)
- [Permutation tensor](../categories/tensor-permutation.md)

## Proof depends on

- [Support preservation](../categories/support-preservation.md)
- [Induced map on ultimate L](../l-theory/ultimate/induced-map.md)
- [Naturality of the excision boundary](../l-theory/ultimate/excision-boundary-naturality.md)

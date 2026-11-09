---
article_id: af_6caba88153522d0d6c90783d
declaration: lemma
origin: background
---

# Collapse inverts the degree-zero inclusion

The [collapse unit](support-collapse-unit.md) $\eta:\mathrm{id}_D\cong\sigma\iota_0$ and the [collapse counit](support-collapse-counit.md) $\varepsilon:\iota_0\sigma\cong\mathrm{id}_{H_b}$ are unitary.

*Proof sketch.* The composite duality functors carry $\xi^{\sigma\iota_0}_X=\xi^\sigma_{\iota_0X}\circ\sigma(\xi^{\iota_0}_X)$ and $\xi^{\iota_0\sigma}_M=\xi^{\iota_0}_{\sigma M}\circ\iota_0(\xi^\sigma_M)$. (1) $\eta$: with $\iota$ and $\pi$ the one-term inclusion and projection, $\xi^{\sigma\iota_0}_X=\pi^*\pi$, so $\eta_X^*\xi^{\sigma\iota_0}_X\eta_{X^*}=\iota^*\pi^*\pi\iota=(\pi\iota)^*(\pi\iota)=1$. (2) $\varepsilon$: the required identity is $\varepsilon_M^*\varepsilon_{M^*}=\xi^{\iota_0\sigma}_M$. In degree $0$ the left side is $\sum_n\pi_n^*\pi_n:\bigoplus_nM_n^*\to(\bigoplus_nM_n)^*$, which is the canonical isomorphism $\xi^\sigma_M$. In every other degree both sides are maps between zero objects.

## Sources

- [Ranicki 1992, §16](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Collapse unit](support-collapse-unit.md)
- [Collapse counit](support-collapse-counit.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)

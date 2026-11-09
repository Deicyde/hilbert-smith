---
declaration: lemma
origin: bridged
---

# Corner identification

In the setting of [Corner duality](corner-duality.md), let $(C_0,\phi_0)$ be a strict symmetric Poincaré complex. Suppose there are chain maps $u:\mathcal C\to C_0$ and $v:C_0\to\mathcal C$ with

$$uv\simeq1,\quad vu\simeq E,\quad uE\simeq u,\quad u\Phi u^*\simeq q\phi_0 .$$

Then $w=u\iota$ is a homotopy equivalence with $w\phi_Dw^*\simeq\phi_0$, and $\operatorname{cls}(D,\phi_D)=\operatorname{cls}(C_0,\phi_0)$.

*Proof sketch.*
1. Put $z=rv$. Then $wz\simeq uEv\simeq uv\simeq1$ and $zw\simeq rE\iota\simeq1$.
2. $w\phi_Dw^*\simeq q^{-1}uE\Phi E^*u^*\simeq q^{-1}u\Phi u^*\simeq\phi_0$, using $uE\simeq u$ and its adjoint.
3. Apply [Homotopy-isometry invariance](../l-theory/A9.md).

## Sources

- HS paper, Section 5.

## Depends on

- [Corner duality](corner-duality.md)

## Proof depends on

- [Homotopy-isometry invariance](../l-theory/A9.md)

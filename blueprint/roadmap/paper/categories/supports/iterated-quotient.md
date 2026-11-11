---
article_id: af_ccb69209a07cf8fd4c9ddaf9
declaration: def
origin: bridged
---

# Iterated quotient

Let $Y,Z\subset S\subset X$ be closed and invariant. The identity on objects and on representatives gives mutually inverse strict duality functors $(\mathcal A_S/\mathcal A_Z)/\mathcal U_Y\cong\mathcal A_S/\mathcal A_{Y\cup Z}$, which commute with the quotient functors from $\mathcal A_S$. The outer quotient is taken by the [quotient support filtration](quotient-support-filtration.md).

*Proof sketch.* A map $[f]$ factors through a $Y$-supported object in $\mathcal A_S/\mathcal A_Z$ iff $f\in I_Y+I_Z$, so the left hom-sets are $\mathrm{Hom}/(I_Y+I_Z)$. $I_Y+I_Z\subset I_{Y\cup Z}$, because $Y$- and $Z$-supported objects are $(Y\cup Z)$-supported and the ideal is closed under sums. Conversely, let $f=hg$ through $W\in\mathcal A_{Y\cup Z}$ whose labels lie in $\overline N_{a_i}(Y\cup Z)$ with $a$ null. Split $W$ into the labels in $\overline N_{a_i}(Y)$, which form a $Y$-supported part, and the rest, which lie in $\overline N_{a_i}(Z)$. Then $f=h\iota_Y\pi_Yg+h\iota_Z\pi_Zg$. Disjointness is not used.

## Sources

- HS paper, Section 6
- New: two-stage quotient identified with one quotient by the union.

## Depends on

- [Quotient support filtration](quotient-support-filtration.md)
- [Support filtration](support-filtration.md)

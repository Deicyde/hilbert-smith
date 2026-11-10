---
article_id: af_75b71a6158a733de114b1305
declaration: theorem
origin: bridged
---

# The two sides of an excision boundary

Let $\mathcal U_A,\mathcal U_B\subset\mathcal A$ be involution-invariant Karoubi filtrations such that both $(\mathcal U_A,\mathcal U_B)$ and $(\mathcal U_B,\mathcal U_A)$ are [excisive pairs](excisive-pair.md), with the common intersection $\mathcal U_Y=\mathcal U_A\cap\mathcal U_B$. Then their [excision boundaries](excision-boundary.md) satisfy
$$\partial_{B,A}=-\partial_{A,B}:\mathbb L_k(\mathcal A)\to\mathbb L_{k-1}(\mathcal U_Y).$$

**Remark (not formalized).** *Status.* This is an open statement: the Lean states it now and proves it later. Its planned route rests on the open statement [Lifting](../../localization/boundary/lift-to-pair.md).

*Planned route.* (1) The swap. For a $\mathcal U_Y$-pair $V_A$ over $(P,\pi)$ for $\mathcal U_Y\subset\mathcal U_A$ and a pair $R$ in $\mathrm{Kar}\,\mathcal U_B$ with boundary $(P,-\pi)$, $R$ is a $\mathcal U_Y$-pair over $(P,-\pi)$ for $\mathcal U_Y\subset\mathcal U_B$, and $V_A$ is a pair in $\mathrm{Kar}\,\mathcal U_A$ with boundary $(P,-(-\pi))$. Exchanging the summands $D_A$ and $D_B$ of the mapping cone is an isomorphism from the [closed union](../../localization/boundary/closed-union.md) $D_A\cup_PR$ to $R\cup_PD_A$ that carries one union structure of the [algebraic union](../../base/pairs/algebraic-union.md) entrywise to the other, because the off-diagonal entries are linear in the boundary structure and change sign twice. So the two closed unions have the same class, and the [union formula](union-formula.md) for both pairs gives $\partial_{A,B}=\mathrm{cls}[P,\pi]$ and $\partial_{B,A}=\mathrm{cls}[P,-\pi]=-\mathrm{cls}[P,\pi]$ on it ([Negation in L](../../base/groups/l-group-neg.md)). (2) Every class is such a union up to $\mathcal U_B$. For $x\in\mathbb L_k(\mathcal A)$, write $r_*(q_B)_*x$ as the class of the image of a $\mathcal U_Y$-pair $V_A$ over $(P,\pi)$, at a finite stage, by [Lifting closed complexes](../../localization/boundary/lift-to-pair-closed.md). [Boundary then inclusion vanishes](composite-zero.md) for $\mathcal U_Y\subset\mathcal U_B$ gives, after finitely many transitions, a null-cobordism $R$ of $(P,-\pi)$ in $\mathrm{Kar}\,\mathcal U_B$. The image of $D_A\cup_PR$ in $\mathcal A/\mathcal U_B$ agrees with $(q_B)_*x$ ([The closed union becomes the image of the pair](../../localization/boundary/union-image.md)), so $x-\mathrm{cls}[D_A\cup_PR]=(i_B)_*w$ by [ultimate exactness in the middle](exact-in-middle.md). (3) Both boundaries vanish on $(i_B)_*w$: $\partial_{A,B}(i_B)_*=0$ because $q_B\circ i_B$ is the zero functor, and $\partial_{B,A}(i_B)_*=\partial'\circ(q'_Y)_*=0$ by the [excision square](excision-square.md) for $(\mathcal U_B,\mathcal U_A)$, $r'_*e'_*=\mathrm{id}$ and exactness of the localization sequence of $\mathcal U_Y\subset\mathcal U_B$ at $\mathbb L_k(\mathcal U_B/\mathcal U_Y)$.

*Known gaps.* The stage bookkeeping of (2), and the statement "boundary after the quotient map is zero" on ultimate L, which no article states yet.

## Sources

- New: the sign of the swap, from the union formula with the closing pieces exchanged.

## Depends on

- [Excisive pair of filtrations](excisive-pair.md)
- [Excision boundary](excision-boundary.md)

## Proof depends on

- [Lifting](../../localization/boundary/lift-to-pair.md)
- [Closing a pair by a null-cobordism of its boundary](../../localization/boundary/closed-union.md)
- [Algebraic union](../../base/pairs/algebraic-union.md)
- [Union formula](union-formula.md)
- [Negation in L](../../base/groups/l-group-neg.md)
- [Lifting closed complexes](../../localization/boundary/lift-to-pair-closed.md)
- [Boundary then inclusion vanishes](composite-zero.md)
- [The closed union becomes the image of the pair](../../localization/boundary/union-image.md)
- [Ultimate exactness in the middle](exact-in-middle.md)
- [Excision square](excision-square.md)

---
article_id: af_dfc41445419e18ecc5f2ae41
declaration: lemma
origin: bridged
---

# Scalar image of the corner

Take the [standing data](../standing-data.md). Let $U_{\rm c}:\mathcal A_{\mathbf G}(T\times S^n)\to\mathcal A_{\mathbf 1}(S^n)$ be [forgetting the control space](../../categories/functors/forget-control.md) for $X=S^n$, and $U'_{\rm c}:\mathcal A_{\mathbf 1}(T\times S^n)\to\mathcal A_{\mathbf 1}(S^n)$ the same functor for the trivial group sequence. Both carry $\mathcal A_{T\times Z_0}$ into $\mathcal A_{Z_0}$ ([forgetting the control space preserves support](../../categories/functors/forget-control-support.md)), so they induce [functors on the exterior quotients](../../categories/supports/exterior-functor.md)
$$U:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n),\qquad U':\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n).$$
For a [graph-type homotopy action](../actions/graph-type-action.md) on $(C,\phi)$, with [corner class](corner-class.md) $\mathfrak d$,
$$U_*\mathfrak d=U'_*\operatorname{cls}(C,\phi).$$

This lemma rests on the open statement [Idempotents split in the bounded homotopy category](kb-idempotent-splitting.md), through the corner class.

*Proof sketch.*
1. $U_*\mathfrak d=\operatorname{cls}(UD,U\phi_D)$ and $U'_*\operatorname{cls}(C,\phi)=\operatorname{cls}(U'C,U'\phi)$ ([the induced map commutes with cls](../../l-theory/ultimate/groups/induced-map-cls.md); $U,U'$ are strict). $(UD,U\iota,Ur)$ splits $UE$, and $U(E\Phi)\simeq U(\Phi E^*)$, because $U$ is a strict duality functor. At level $i$, $U\operatorname{Ind}C=\bigoplus_{s\in G_i}U'C$, sheet by sheet.
2. Let $j_0,\pi_0$ be the inclusion and projection of sheet $0$, and put $v=UE\,j_0$ and $u=q\pi_0UE$. The block of $E$ from sheet $b$ to sheet $a$ is $E_{ab}=q^{-1}A_{b-a}$, so $u_b=A_b$ and $v_a=q^{-1}A_{-a}$.
3. Check the relations of [Corner identification](corner-identification.md) for $C_0=U'C$, $\phi_0=U'\phi$; put $\varepsilon_i=2\delta_i+\operatorname{prop}\phi_i\to0$:
   - $uv=qE^2_{00}\simeq qE_{00}=A_0=1$ and $uE\simeq u$: apply $U$, $q\pi_0$ and $j_0$ to $E^2\simeq E$ ([Average is a compatible idempotent](../actions/average-compatible-idempotent.md)).
   - $vu\simeq E$: the blocks $q^{-1}(A_{-a}A_b-A_{b-a})$ equal $d\beta+\beta d$ plus witnesses, with $\beta_{ab}=q^{-1}B_{-a,b}$. [Sheet blocks after forgetting](../actions/sheet-block-propagation.md) bounds the propagation of $\beta$ by $\delta_i$, and [Sums of witnesses](../actions/witness-sum.md) with $a_k=j_a$, $b_k=\pi_b$ puts the defect in $\mathcal A_{Z_0}$.
   - $u\Phi u^*=\sum_bA_b\phi A_b^*\simeq\sum_b\phi(A_bA_{-b})^*\simeq q\phi$, with homotopies $\sum_bV_bA_b^*$ and $\sum_b\phi B_{b,-b}^*$. By the [calculus of graph types](../actions/graph-type-calculus.md), $V_bA_b^*$ has type $\chi_i(b)-\chi_i(b)=0$ with bound $2\delta_i$ and $\phi B_{b,-b}^*$ has type $0$ with bound $\delta_i+\operatorname{prop}\phi_i$, so both have propagation at most $\varepsilon_i$. The defects (witnesses composed with $A_b^*$, $V_b$ or $\phi$) are witnesses with bound $\varepsilon_i$, summed by [Sums of witnesses](../actions/witness-sum.md).
4. Apply [Corner identification](corner-identification.md).

## Sources

- HS paper, Section 5 (scalar normalization) and Section 11.

## Depends on

- [Standing data](../standing-data.md)
- [The corner class](corner-class.md)
- [Forgetting the control space](../../categories/functors/forget-control.md)
- [Forgetting the control space preserves support](../../categories/functors/forget-control-support.md)
- [Induced functor on exterior quotients](../../categories/supports/exterior-functor.md)

## Proof depends on

- [Corner identification](corner-identification.md)
- [Average is a compatible idempotent](../actions/average-compatible-idempotent.md)
- [Sheet blocks after forgetting](../actions/sheet-block-propagation.md)
- [Sums of witnesses](../actions/witness-sum.md)
- [Calculus of graph types](../actions/graph-type-calculus.md)
- [Sheet shifts multiply](../actions/sheet-shift-mul.md)
- [The induced map commutes with cls](../../l-theory/ultimate/groups/induced-map-cls.md)

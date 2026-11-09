---
article_id: af_dfc41445419e18ecc5f2ae41
declaration: lemma
origin: bridged
---

# Scalar image of the corner

Let $U:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ and $U':\mathcal B_{\mathbf 1,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ forget the group (if any) and push labels forward along the projection to $S^n$. For a graph-type homotopy action on $(C,\phi)$,
$$U_*\mathfrak d=U'_*\operatorname{cls}(C,\phi).$$

*Proof sketch.*
1. $U_*\mathfrak d=\operatorname{cls}(UD,U\phi_D)$ ([Functoriality](../../l-theory/ultimate/groups/induced-map.md)), and $(UD,U\iota,Ur)$ splits $UE$ compatibly. A graph-type bound $\delta$ gives sphere propagation at most $\delta$, and a witness over $Z$ is one over $Z_0$.
2. Put $v=UE\,j_1$ and $u=q\pi_1UE$, so $u_b=A_b$, $v_a=q^{-1}A_{a^{-1}}$, $E_{ab}=q^{-1}A_{a^{-1}b}$.
3. Check the relations of [Corner identification](corner-identification.md); put $\varepsilon_i=2\delta_i+\operatorname{prop}\phi_i\to0$:
   - $uv=qE^2_{11}\simeq qE_{11}=A_1=1$ and $uE\simeq u$: apply $U$, $q\pi_1$, $j_1$ to $E^2\simeq E$ ([Average is a compatible idempotent](../actions/average-compatible-idempotent.md)).
   - $vu\simeq E$: the blocks $q^{-1}(A_{a^{-1}}A_b-A_{a^{-1}b})$ equal $d\beta+\beta d$ plus witnesses, with $\beta_{ab}=q^{-1}B_{a^{-1},b}$. [Sheet blocks after forgetting](../actions/sheet-block-propagation.md) bounds $\beta$ by $\delta_i$, and [Sums of witnesses](../actions/witness-sum.md) with $a=j_a$, $b=\pi_b$ puts the defect in $\mathcal A_{Z_0}$.
   - $u\Phi u^*=\sum_bA_b\phi A_b^*\simeq\sum_b\phi(A_bA_{b^{-1}})^*\simeq q\phi$, with homotopies $\sum_bV_bA_b^*$ and $\sum_b\phi B_{b,b^{-1}}^*$ of propagation at most $\varepsilon_i$; the defects (witnesses composed with $A_b^*$, $V_b$ or $\phi$) are witnesses with bound $\varepsilon_i$, summed by [Sums of witnesses](../actions/witness-sum.md).
4. Apply [Corner identification](corner-identification.md).

## Sources

- HS paper, Section 5 (scalar normalization) and Section 11.

## Depends on

- [The corner class](corner-class.md)
- [Forgetting the group](../../categories/functors/forget-group.md)
- [Pushforward of labels](../../categories/functors/pushforward.md)

## Proof depends on

- [Corner identification](corner-identification.md)
- [Sheet blocks after forgetting](../actions/sheet-block-propagation.md)
- [Sums of witnesses](../actions/witness-sum.md)
- [Sheet shifts multiply](../actions/sheet-shift-mul.md)
- [Functoriality](../../l-theory/ultimate/groups/induced-map.md)

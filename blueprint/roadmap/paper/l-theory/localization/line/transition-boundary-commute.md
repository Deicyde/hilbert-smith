---
article_id: af_04f0beb6ade57df21bba8a0f
declaration: lemma
origin: background
---

# Transition commutes with the boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. For $j\ge0$ and $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$,
$$t\big(\partial^{(j)}x\big)=\eta_{k+j+1}\,\partial^{(j+1)}(t\,x),$$
where on the left $t$ is the [transition map](transition-map.md) of $\mathcal U$ at level $j+1$, on the right that of $\mathcal A/\mathcal U$ at level $j$, and $\eta$ is [the line sign](line-sign.md). Since $\eta_{k+j+1}=1$, $t\circ\partial^{(j)}=\partial^{(j+1)}\circ t$.

*Proof sketch.*
1. Lift. Let $x=[C,\phi]$. By the definition of the [localization boundary](../sequence/localization-boundary.md), there is a strict pair $(f:P\to D,\delta\phi,\phi_P)$ in $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$ with $P$ in $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal U$ and $[q^{(j+1)}D]=t^{\mathrm{im}}x$ in $L^{\mathrm{im}}_{k+j+1}$, and $\partial^{(j)}x=[P,\phi_P]$. The pair has dimension $k+j+1$, because $t^{\mathrm{im}}x$ lies in $L^{\mathrm{im}}_{k+j+1}$.
2. Product. By [Product of a pair with the line](product-with-line.md), $(f\otimes1:P\otimes\Lambda\to D\otimes\Lambda,\delta\phi\otimes\lambda,\phi_P\otimes\lambda)$ is a strict $(k+j+2)$-dimensional pair in $\operatorname{Kar}C_{\mathbb Z^{j+2}}\mathcal A$, with boundary $(P\otimes\Lambda,\phi_P\otimes\lambda)$ and no sign. This is $\eta_{k+j+1}=1$; the index is the dimension of the pair. $P\otimes\Lambda$ lies in $\operatorname{Kar}C_{\mathbb Z^{j+2}}\mathcal U$, since $\boxtimes$ carries objects of $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal U$ to objects of $\operatorname{Kar}C_{\mathbb Z^{j+2}}\mathcal U$. Both sides add the coordinate $j+2$ as the outermost one, so no coordinate swap is needed.
3. It lifts $t^{\mathrm{im}}(tx)$. Apply $(e_{j+1})_*\circ\mathrm{fgt}$ to $[q^{(j+1)}D]=t^{\mathrm{im}}x$: by [Transitions and quotients](transition-quotient.md), $[(C_{\mathbb Z^{j+1}}q)D]=t\,x$ in $L^p_{k+j+1}(C_{\mathbb Z^{j+1}}(\mathcal A/\mathcal U))$. Hence $t^{\mathrm{im}}[(C_{\mathbb Z^{j+1}}q)D]=t^{\mathrm{im}}(tx)$. On the other side, $q^{(j+2)}=e_{j+2}^{-1}C_{\mathbb Z^{j+2}}(q)$ (functor equation of that article), and the isomorphism $\omega$ of [Naturality of the transition](transition-naturality.md), step 1, for $F=q$ identifies $C_{\mathbb Z^{j+2}}(q)(D\otimes\Lambda)$ with $(C_{\mathbb Z^{j+1}}q)D\otimes\Lambda$, structures included. After $e_{j+2}^{-1}$ both ends are decorated ([Products with the line are decorated](line-product-decorated.md)), so the cylinder cobordism is decorated and $[q^{(j+2)}(D\otimes\Lambda)]=t^{\mathrm{im}}[(C_{\mathbb Z^{j+1}}q)D]=t^{\mathrm{im}}(tx)$.
4. By the definition of $\partial$ (any lift; [Independence of the lift](../sequence/boundary-independence.md)), $\partial^{(j+1)}(tx)=\partial\,t^{\mathrm{im}}(tx)=[P\otimes\Lambda,\phi_P\otimes\lambda]=t[P,\phi_P]=t(\partial^{(j)}x)$.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md); [Carlsson-Pedersen 1995, §4](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the lift of $t^{\mathrm{im}}x$ times the line, with the sign computed in this paper's conventions.

## Depends on

- [Level boundary](level-boundary.md)
- [Transition map](transition-map.md)
- [The line sign](line-sign.md)

## Proof depends on

- [Product of a pair with the line](product-with-line.md)
- [Transitions and quotients](transition-quotient.md)
- [Naturality of the transition](transition-naturality.md)
- [Products with the line are decorated](line-product-decorated.md)
- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)
- [Independence of the lift](../sequence/boundary-independence.md)

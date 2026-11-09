---
article_id: af_ee8eddd8c9c18df91f7e6233
declaration: lemma
origin: bridged
---

# The truncated line computes the quotient image

Let $x=(C,\phi)$ be as in [The truncated line is a pair](truncated-line-pair.md), let $q_b:H_+\to H_+/H_b$ and $q:C_\mathbb Z(D)\to C_\mathbb Z(D)/H_-$ be the quotient functors, and let $e$ be the [inclusion of the half-line quotient](../bounded/half-lines/half-line-quotient-inclusion.md). Let $y\in L^{\mathrm{im}}_{m+1}(H_+/H_b)$ be the class of the [image](../localization/sequence/image-pair.md) of the pair $(x\otimes\mathrm{pt}_0\to x\otimes\Lambda_+)$. Then $\mathrm{Kar}\,e$ carries decorated objects to decorated objects, and the [decorated induced map](../localization/sequence/decorated-induced-map.md) satisfies $e^{\mathrm{im}}_*y=q_*\,t\,x$ in $L^{\mathrm{im}}_{m+1}(C_\mathbb Z(D)/H_-)$, where $t$ is the [transition map](../localization/line/transition-map.md) and $q_*$ the [quotient map](../localization/sequence/quotient-map.md).

*Proof sketch.*
1. Decorations. If $M$ is decorated in $\mathrm{Kar}(H_+/H_b)$, then $[M]=[q_bQ]$ with $Q$ in $\mathrm{Kar}\,H_+$. By [$K_0$ of a half-line vanishes](../bounded/half-lines/half-line-k-swindle.md) and [Equality in $K_0$](../bounded/categories/k-zero-stable-equality.md), $Q\oplus X\cong X$ for an object $X$ of $H_+$, so $eM\oplus eq_bX\cong eq_bX$ and $[eM]=0$, which is decorated.
2. The inclusion. $e\,q_b=q$ on $H_+$. In each position $x\otimes\Lambda=(x\otimes\Lambda_+)\oplus(x\otimes\Lambda_{<0})$, where $\Lambda_{<0}$ is spanned by the cells at positions $n<0$, and $x\otimes\Lambda_{<0}$ lies in $H_-$. So the inclusion $i:x\otimes\Lambda_+\to x\otimes\Lambda$ becomes an isomorphism $q(i)$, with inverse the class of the projection.
3. Structures. Let $\Phi_+$ and $\Phi$ be the structures of $x\otimes\Lambda_+$ ([Product with a pair](../localization/line/product-with-pair.md)) and of $x\otimes\Lambda$ ([Product with the line](../localization/line/product-with-line.md)); both are the tensor product of $\phi$ with $\delta\phi_0$, respectively $\varphi_0$. So $i\Phi_+i^*-\Phi$ consists of the components with source or target a cell at a position $n<0$, including the propagation-$1$ terms $v_0^*\mapsto\tfrac12e_{-1/2}$ and $e_{-1/2}^*\mapsto\tfrac12v_0$. Each passes through $x\otimes\Lambda_{<0}\in H_-$, so $q(i)_\%(q\Phi_+)=q\Phi$.
4. Cobordism. [Homotopy-isometric complexes are cobordant](../base/pairs/cylinder-cobordism.md), with $\mathcal P$ the decorated objects, $h=q(i)$ and $\chi=0$, gives a cobordism with decorated chain objects: they are images of objects of $\mathrm{Kar}\,C_\mathbb Z(D)$. Hence $[e\,q_b(x\otimes\Lambda_+),e\,q_b\Phi_+]=[q(x\otimes\Lambda),q\Phi]$ in $L^{\mathrm{im}}_{m+1}$, which is $e^{\mathrm{im}}_*y=q_*tx$ since $e$ is strict.

## Sources

- New: the line is two rays glued at a point, read modulo $H_-$.

## Depends on

- [The truncated line is a pair](truncated-line-pair.md)
- [Inclusion of the half-line quotient](../bounded/half-lines/half-line-quotient-inclusion.md)
- [Image of a pair](../localization/sequence/image-pair.md)
- [Decorated induced map](../localization/sequence/decorated-induced-map.md)
- [Transition map](../localization/line/transition-map.md)
- [Quotient map](../localization/sequence/quotient-map.md)

## Proof depends on

- [$K_0$ of a half-line vanishes](../bounded/half-lines/half-line-k-swindle.md)
- [Equality in $K_0$](../bounded/categories/k-zero-stable-equality.md)
- [Product with a pair](../localization/line/product-with-pair.md)
- [Product with the line](../localization/line/product-with-line.md)
- [Homotopy-isometric complexes are cobordant](../base/pairs/cylinder-cobordism.md)

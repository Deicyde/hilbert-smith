---
article_id: af_66073425b52767036e3b4ef8
declaration: lemma
origin: background
statement: formalized
lean: HSP.decTransitionCx_sum
---

# The decorated transition is additive

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. For strict $m$-dimensional symmetric Poincaré complexes $(C,\phi)$ and $(C',\phi')$ in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$, the [decorated product with the line](decorated-line-product.md) of $(C\oplus C',\phi\oplus\phi')$ has the class of the sum of the decorated products of $(C,\phi)$ and $(C',\phi')$ in $L^{\mathrm{im}}_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A/C_{\mathbb Z^{j+1}}\mathcal U)$.

*Proof sketch.* The canonical isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ carries structures exactly. [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md), with $\mathcal P$ the decorated objects (closed under sums and duals) and $\chi=0$, gives a cobordism whose chain objects are decorated.

## Sources

- New: step 3 of the decorated transition, split out.

## Depends on

- [Decorated product with the line](decorated-line-product.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)

## Proof depends on

- [Homotopy-isometric complexes are cobordant](../../base/pairs/cylinder-cobordism.md)

---
article_id: af_2d9b476545814d3fb36aa28c
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.cxProd_line_decorated
---

# Products with the line are decorated

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. For every complex $C$ in $\operatorname{Kar}C_{\mathbb Z^j}(\mathcal A/\mathcal U)$ with finitely many nonzero chain objects ($\Lambda$ has finitely many nonzero chain objects too), every chain object $X$ of $C\otimes\Lambda$ has $[X]=0$ in $K_0(\operatorname{Kar}C_{\mathbb Z^{j+1}}(\mathcal A/\mathcal U))$. Hence $(\operatorname{Kar}e_{j+1}^{-1})(X)$ is [decorated](../decorations/decorated-object.md) for the filtration $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$.

*Proof sketch.*
1. $(C\otimes\Lambda)_r=C_r\boxtimes\Lambda_0\oplus C_{r-1}\boxtimes\Lambda_1$, and each $\Lambda_i$ holds $\mathbb Q$ in every position. So $N\boxtimes\Lambda_i$ is isomorphic, by a map of propagation $0$, to the constant object $c(N)$.
2. $[c(N)]=0$ by [Constant objects have class zero](../../bounded/half-lines/constant-object-class.md), applied to $\mathcal A/\mathcal U$. The class is additive, so $[X]=0$.
3. $e_{j+1}^{-1}$ is an isomorphism of categories ([Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)), so $\operatorname{Kar}e_{j+1}^{-1}$ preserves sums and induces a homomorphism on $K_0$. The class of $(\operatorname{Kar}e_{j+1}^{-1})(X)$ is therefore $0=[q0]$, the class of the image of a zero object, so it is decorated.

## Sources

- New: each chain object is a sum of constant objects, whose classes vanish by two half-line swindles.

## Depends on

- [Iterated bounded subcategories are closed under sums and duals](../../bounded/categories/iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)
- [Box product on iterated bounded categories](../products/box-pairing-pow.md)
- [Tensor product of complexes](../products/complex-product.md)
- [The symmetric line](../products/symmetric-line.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
- [Duals of box products](../products/box-dual.md)

## Proof depends on

- [Constant objects have class zero](../../bounded/half-lines/constant-object-class.md)
- [$K_0$ of an idempotent completion](../../bounded/categories/k-zero.md)

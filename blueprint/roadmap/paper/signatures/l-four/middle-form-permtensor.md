---
article_id: af_5f5e114bf4922737c86c8663
declaration: lemma
origin: bridged
---

# Middle form of a permutation tensor

Let $X$ be a finite $G$-set. There is a $G$-equivariant isometry $\mathbb R[X]\otimes H^2(C;\mathbb R)\to H^2(\tau_XC;\mathbb R)$ from $s_X\otimes b_C$ to $b_{\tau_XC}$. Here $G$ acts diagonally on the source.

*Proof sketch.* $\tau_X(B,e)=(X\times B,1\otimes e)$, so the real cochains of $\tau_XC$ are $\mathbb R[X]\otimes\mathrm{im}(e^T)$ with coboundary $1\otimes d^T$. The functor $\mathbb R[X]\otimes-$ is exact, so $u\otimes[y]\mapsto[u\otimes y]$ is an isomorphism on $H^2$. The structure is $(\tau_X)_\%\varphi=1\otimes\varphi$, and the standard pairing on $\mathbb R^{X\times B}$ is the product of the standard pairings. So $b_{\tau_XC}(u\otimes x,u'\otimes y)=s_X(u,u')\,b_C(x,y)$. The map commutes with $g(x,b)=(gx,gb)$.

## Sources

- HS paper, Section 3

## Depends on

- [The middle form](middle-form.md)
- [Permutation tensor](../point-functors/permutation-tensor.md)

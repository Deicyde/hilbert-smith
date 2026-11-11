---
article_id: af_1bd5ce938587df17b51eefc7
declaration: lemma
origin: bridged
---

# Constant objects have class zero

For an object $N$ of $\mathrm{Kar}\,C_{\mathbb Z^j}(A)$, let $c(N)$ be the object of $\mathrm{Kar}\,C_{\mathbb Z^{j+1}}(A)$ with $N$ in every degree and diagonal idempotent. Then $[c(N)]=0$ in $K_0(\mathrm{Kar}\,C_{\mathbb Z^{j+1}}(A))$.

*Proof sketch.* Take $D=C_{\mathbb Z^j}(A)$, so that $C_{\mathbb Z^{j+1}}(A)=C_\mathbb Z(D)$. $c(N)$ is the sum of its truncations $P_+$ to $n\ge0$ and $P_-$ to $n<0$, which are objects of $\mathrm{Kar}\,H_+$ and $\mathrm{Kar}\,H_-$. By [$K_0$ of a half-line vanishes](half-line-k-swindle.md) and [Equality in $K_0$](../categories/k-zero-stable-equality.md), $P_\pm\oplus M_\pm\cong M_\pm$ for objects $M_\pm$ of $H_\pm$. These isomorphisms hold in $\mathrm{Kar}\,C_\mathbb Z(D)$, so $[P_+]=[P_-]=0$ there and $[c(N)]=[P_+]+[P_-]=0$.

## Sources

- New: two half-line swindles.

## Depends on

- [Iterated bounded categories](../categories/iterated-bounded-category.md)
- [$K_0$ of an idempotent completion](../categories/k-zero.md)

## Proof depends on

- [$K_0$ of a half-line vanishes](half-line-k-swindle.md)
- [Equality in $K_0$](../categories/k-zero-stable-equality.md)

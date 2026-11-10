---
article_id: af_ec5f0ed895dab34339abfa7b
declaration: lemma
origin: cited
---

# The bounded swindle

For every object $F$ of $C_\mathbb Z(A)$ there is an object $G$ of $C_\mathbb Z(A)$ with $F\oplus G\cong G$.

*Proof sketch.* Write $F=F_{\ge0}\oplus F_{<0}$, where $F_{\ge0}$ keeps the degrees $n\ge0$ and has a chosen zero object in the degrees $n<0$, and $F_{<0}$ the reverse. Put $G^+_n=\bigoplus_{k=0}^{n}F_{n-k}$ for $n\ge0$, and let $G^+_n$ be a chosen zero object for $n<0$. Then $G^+\cong F_{\ge0}\oplus\Sigma G^+$ with propagation $0$, where $\Sigma$ is the shift by one. The identity matrices give $\Sigma G^+\cong G^+$ with propagation $1$. The mirror construction handles $F_{<0}$. Take $G=G^+\oplus G^-$.

## Sources

- [Pedersen-Weibel 1985, Eilenberg swindle](../../../../../sources/paper/pedersen-weibel-1985.md) [U]

## Depends on

- [The bounded category](bounded-category.md)

---
article_id: af_dfeab2cef4882cd963cad5c4
declaration: def
origin: background
---

# Truncation to the positive half-line

Fix a zero object $0$ of $D$. Let $\tau:C_\mathbb Z(D)/H_-\to H_+/H_b$ send $M$ to $M_{\ge0}$, which is $M_n$ in degrees $n\ge0$ and $0$ in degrees $n<0$, and send $[f]$ to $[(f_{mn})_{m,n\ge0}]$. Let $\xi_M:\tau(M^*)\to\tau(M)^*$ be the class of the matrix that is the identity in degrees $n\ge0$ and the unique isomorphism $0\to0^*$ in degrees $n<0$. Then $(\tau,\xi)$ is a well-defined duality functor.

*Proof sketch.* Let $f$ have propagation $r$. Then $\tau(gf)-\tau(g)\tau(f)$ passes through the degrees $[-r,-1]$ of the middle object, which form an object of $H_b$. If $f=gh$ passes through $N\in H_-$, with $N_n$ a zero object for $n>R$, then $\tau(f)$ passes through the window $N_{[-r,R]}\in H_b$. So $\tau$ is well defined and functorial mod $H_b$. Truncation commutes with the degreewise duality in degrees $n\ge0$; $\xi$ is natural, and $\xi_M^*=\xi_{M^*}$ because in degrees $n<0$ both sides are maps between zero objects.

## Sources

- [Carlsson-Pedersen 1995, excision](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Half-lines are Karoubi filtrations](half-line-filtration.md)
- [Bounded support is a Karoubi filtration of a half-line](bounded-support-filtration.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Duality functor](../../base/categories/duality-functor.md)

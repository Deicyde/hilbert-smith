---
article_id: af_c55b6634ff4b2eba26290b5d
declaration: def
origin: background
---

# Completion of a subcategory

For a full additive $\mathcal U\subset\mathcal A$ with $\mathcal U^*\subset\mathcal U$, $\mathrm{Kar}\,\mathcal U\subset\mathrm{Kar}\,\mathcal A$ is the full subcategory of objects $(M,e)$ such that $e$ factors through an object of $\mathcal U$.

**Remark (not formalized).** (a) $(M,e)\in\mathrm{Kar}\,\mathcal U$ iff $(M,e)\cong(V,r)$ for some $V\in\mathcal U$. $\mathrm{Kar}\,\mathcal U$ is closed under $*$ ($e^*$ factors through $V^*$), under finite sums ($e\oplus e'$ factors through $V\oplus V'$), and under retracts: if $i:(N,e')\to(M,e)$ and $s:(M,e)\to(N,e')$ satisfy $si=e'$, then $e'=sei$ factors through $V$.

(b) $\mathrm{Kar}\,\mathcal U\subset\mathrm{Kar}\,\mathcal A$ need not be an involution-invariant Karoubi filtration when $\mathcal U\subset\mathcal A$ is one. Take $R=\mathbb Q[x,y]/(y^2-x^3-x^2)$ with trivial involution, $\mathcal A=C_{\mathbb Z}(\mathrm{Free}\,R)$, and $\mathcal U$ the objects supported in some $(-\infty,a]$. The cuts $M=M_{\le a}\oplus M_{>a}$ make $\mathcal U$ a filtration. Suppose $\mathrm{Kar}\,\mathcal U$ were one. For $(M,e)$, factorization applied to $e\circ i_a:(M_{\le a},1)\to(M,e)$ gives $q$ with $(e-q)i_a=0$. Then $(M,e)=(M,q)\oplus(M,e-q)$, with $(M,q)$ supported in $(-\infty,a]$ and $(M,e-q)$ supported in $(a,\infty)$, up to isomorphism. Eilenberg swindles kill both classes in $K_0(\mathrm{Kar}\,\mathcal A)\cong K_{-1}(R)$ [U: Pedersen-Weibel 1985]. But $K_{-1}(R)\ne0$ for the node [U: Weibel, The K-book, Ch. III], a contradiction.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the counterexample in (b)

## Depends on

- [Idempotent completion with duality](karoubi-duality.md)
- [Quotient by a subcategory](filtration-quotient.md)

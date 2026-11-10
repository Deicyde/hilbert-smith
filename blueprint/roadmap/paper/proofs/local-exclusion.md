---
article_id: af_251cccb60e3303ff0ab37e1a
declaration: theorem
origin: bridged
---

# Local exclusion

Let $p$ be a prime, $n\in\mathbb N$, and $O\subseteq\mathbb{R}^n$ a nonempty connected open set. No jointly continuous action of $\mathbb{Z}_p$ on $O$ is faithful.

*Proof sketch.*
1. If $n=0$, $O$ is a point, and $0$ and $1$ act alike.
2. Otherwise suppose the action is faithful. $O$ is a connected $n$-manifold, so it carries fixed local data with $D=1/64$, with buffer radii $r<R<t<u$ and control space $T$.
3. $T$ is compact, $d_T$ is a metric inducing its topology, and $C_p$ acts on it freely and isometrically. So $p$, $G_i=\mathbb Z/p^i$ with $\chi_i$ reduction modulo $p$ ($i\ge1$), $T$, $n$ and the radius $R$ form standing data, with $Z_0$, $Z=T\times Z_0$ and $N=n+4$ as defined there.
4. Theorem C gives the compressed complex $(C,\hat\varphi)$: a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, with a graph-type homotopy action of $\mathbf G=(G_i,\chi_i)$, and $U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}$, the class of the torus test map.
5. Theorem A, applied to $(C,\hat\varphi)$, gives $\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}\mathfrak m_{f_T})\in p\,\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$.
6. Theorem B for the test map gives $\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}\mathfrak m_{f_T})=[(\varepsilon,\varepsilon,\dots)]$ with $\varepsilon=\pm1$.
7. By steps 5 and 6 there are integers $t_i$ with $\varepsilon=p\,t_i$ for all large $i$. The lemma on integer tails, for the constant sequence $s_i=\varepsilon$, gives a contradiction.

This proof rests on open statements: through the fixed local data, on [Newman's theorem on fixing an open set](../inputs/newman/newman-open-set.md); through Theorems A and B, on the open statements those rest on, among them [Lemma U](../l-theory/comparison/lemma-u.md) and [idempotent splitting in the bounded homotopy category](../corner/theorem/kb-idempotent-splitting.md).

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (Proposition 13.1 and the proof of Theorem 1.1)
- [HS paper, Section 4](../../../sources/hs-paper.md#section-4-divisibility-over-a-free-c_p-space-algobstruction-lines-317-380)
- New: the contradiction is assembled from Theorems A, B and C as stated in this paper, with $T$ the control space of the fixed local data

## Depends on

## Proof depends on

- [Fixed local data from a faithful action](../local-data/control/fixed-local-data-exists.md)
- [The control space is compact](../local-data/control/control-space-compact.md)
- [The orbit metric metrizes the control space](../local-data/control/control-metric-properties.md)
- [The cyclic action is free](../local-data/control/control-action-free.md)
- [The cyclic action is isometric](../local-data/control/control-action-isometric.md)
- [Standing data](../corner/standing-data.md)
- [Theorem C](../compression/theorem-c.md)
- [Theorem A](../corner/theorem/theorem-a.md)
- [Theorem B for the test map](../evaluation/theorem-b-test-map.md)
- [The tail signature](../signatures/tail/tail-signature.md)
- [Integer tails](integer-tails.md)

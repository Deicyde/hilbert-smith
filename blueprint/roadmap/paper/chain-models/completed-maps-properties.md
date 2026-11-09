---
declaration: lemma
origin: bridged
---
# Properties of completed maps

1. There is a nondecreasing $\omega$ with $\omega(t)\ge t$ and $\omega(t)\to0$ as $t\to0$, such that $d_\infty(Lx,Lx')\le\omega(d_\infty(x,x'))$ for all $L\in\mathcal F$.
2. Every $L\in\mathcal F$ moves points by at most $2D$ in $d_2$, and is the identity off $\overline B(0,3/2)$.
3. $\widehat a=a\cdot{}$ on $\overline B(0,1)$, and $f_T\widehat a=f_T$.
4. $f_T$ is continuous, hence uniformly continuous with a modulus $\omega_f$, and $f_T=\infty$ off $B(0,17/64)$.
5. Put $\beta_i=\sup\{|r_i(g)\cdot(r_i(h)\cdot x)-r_i(g+h)\cdot x|: g,h\in G_i,\ |x|\le3/8\}$. Then $\beta_i\to0$. For $|x|\le3/8$, each point $L_{r_i(g),r_i(h),r_i(g+h),t}(x)$ lies within $\beta_i$ of $r_i(g+h)\cdot x$.

*Proof sketch.* (1) The evaluation map $\mathbb Z_p^3\times[0,1]\times T^n\to T^n$ is continuous on a compact space. (2) $\widehat a$ moves points by at most $D$, so the track moves them by at most $(1-t)2D+tD$. (3) Use $\theta=1$ on $\overline B(0,1)$ and [invariance](../local-data/chart/test-map-invariant.md). For $1<|x|<3/2$, both $x$ and $\widehat ax$ have norm at least $1-D$, and $f=\infty$ there by (4). (4) [Continuity](../local-data/chart/test-map-continuous.md) of $f$, and $f=\infty$ near $\partial[-2,2]^n$. If $f(x)\ne\infty$, then $x\in U^+$ by [preimages](../local-data/chart/test-map-proper.md), and $U^+\subseteq\overline B(0,\rho_++D)\subseteq B(0,17/64)$ by [boundedness](../local-data/chart/test-region-bounded.md). (5) [Representatives act approximately](../local-data/control/representatives.md), applied to the compact invariant set $\mathbb Z_p\cdot\overline B(0,3/8)\subseteq B(0,2)$. For $|x|\le3/8$, each factor acts as itself, and the track lies on the segment from $r(g)r(h)x$ to $r(g+h)x$.

## Sources
- HS paper, Section 9; it transfers.
## Depends on
- [Track maps](track-map.md)
- [Torus test map](torus-test-map.md)
## Proof depends on
- [Test map invariant](../local-data/chart/test-map-invariant.md), [test map continuous](../local-data/chart/test-map-continuous.md), [preimages](../local-data/chart/test-map-proper.md), [bounded](../local-data/chart/test-region-bounded.md), [representatives](../local-data/control/representatives.md)

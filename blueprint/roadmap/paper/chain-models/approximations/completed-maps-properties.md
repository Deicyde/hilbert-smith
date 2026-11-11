---
article_id: af_d20fc210f0f23765b2215e6e
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.completedMaps_properties
---
# Properties of completed maps

Fix a [local datum](../../local-data/chart/local-datum.md) and $0<\rho<\rho_+$, and let $f_T$ be the [torus test map](torus-test-map.md) of radius $\rho$. A property holds off $\overline B(0,r)$ if it holds at the points $x$ of $\mathbb T^n$ with $|\tilde x|>r$, and off $B(0,r)$ if it holds where $|\tilde x|\ge r$.

1. The [modulus](modulus.md) $\omega$ is nondecreasing, $\omega(t)\ge t$, $\omega(t)\to0$ as $t\to0$, and $d_\infty(Lx,Lx')\le\omega(d_\infty(x,x'))$ for all $L\in\mathcal F$ and $x,x'\in\mathbb T^n$.
2. Every $L\in\mathcal F$ moves points by at most $2D$ in $d_2$, and is the identity off $\overline B(0,3/2)$.
3. $\widehat a=a\cdot{}$ on $\overline B(0,1)$, and $f_T\widehat a=f_T$.
4. $f_T$ is continuous, and uniformly continuous for the round metric $d_S$ of the [round sphere](../../corner/round-sphere.md), so it has a modulus $\omega_f$; and $f_T=\infty$ off $B(0,17/64)$.
5. Put $\beta_i=\sup\{|r_i(g)\cdot(r_i(h)\cdot x)-r_i(g+h)\cdot x|: g,h\in\mathbb Z/p^i,\ x\in\Omega,\ |x|\le3/8\}$. Then $\beta_i\to0$. For $x\in\Omega$ with $|x|\le3/8$, each point $L_{r_i(g),r_i(h),r_i(g+h),t}(x)\in\mathbb R^n$ lies within $\beta_i$ of $r_i(g+h)\cdot x$.

*Proof sketch.* (1) Monotonicity, $\omega(t)\ge t$ and the modulus inequality are read off the formula, since the set of oscillations contains only distances and grows with $t$. The evaluation map $\mathbb Z_p^3\times[0,1]\times\mathbb T^n\to\mathbb T^n$ is continuous: $(a,y)\mapsto\widehat a(y)$ is continuous on $\mathbb Z_p\times\mathbb R^n$ (on $B(0,2)$ by the continuity of the action, and off $\overline B(0,3/2)$ it is the identity), the lift is continuous where $|\tilde x|_\infty<2$, and near the other points the track maps are the identity. On a compact space it is uniformly continuous, so the supremum tends to $0$ with $t$. (2) $\widehat a$ moves points by at most $D$, so the track moves them by at most $(1-t)2D+tD$, and $d_2(q(y),q(y'))\le|y-y'|$. Off $\overline B(0,3/2)$ every $\widehat a$ is the identity. (3) Use $\theta=1$ on $\overline B(0,1)$. For $|\tilde x|\ge3/2$, $\widehat a$ fixes $x$. Otherwise $|\widehat a\tilde x|<3/2+D<2$, so $\widehat a\tilde x$ is the lift of $\widehat ax$. For $|\tilde x|\le1$ use [invariance](../../local-data/chart/test-map-invariant.md). For $1<|\tilde x|<3/2$, both $\tilde x$ and $\widehat a\tilde x$ have norm at least $1-D\ge17/64$, and $f=\infty$ there by (4). (4) If $|y|\ge17/64$ and $y\in\Omega$, then $|F_0(y)|\ge|y|-D\ge1/4>\rho$ ([averaged map displacement](../../local-data/chart/averaged-map-displacement.md)), so $f(y)=\infty$. Hence $f_T$ is continuous: where $|\tilde x|_\infty<2$ it is [continuous](../../local-data/chart/test-map-continuous.md) $f$ composed with the continuous lift, and elsewhere $f_T=\infty$ nearby. Uniform continuity holds because $\mathbb T^n$ is compact and $d_S$ induces the topology of $S^n$. (5) [Representatives act approximately](../../local-data/control/representatives.md), applied to the compact invariant set $\mathbb Z_p\cdot\overline B(0,3/8)\subseteq\Omega$; each $\beta_i$ is finite, as the defects are at most $3D$. For $|x|\le3/8$, each factor acts as itself ($|r_i(h)\cdot x|\le3/8+D\le1$), and $L(x)-r(g+h)x=(1-t)(r(g)r(h)x-r(g+h)x)$.

## Sources
- HS paper, Section 9; it transfers.
## Depends on
- [The track oscillation is bounded](maps/track-oscillation-bounded.md)
- [Track oscillation](maps/track-oscillation.md)
- [The track family](maps/track-family.md)
- [Completed and track maps are the identity off B(0,3/2)](maps/identity-off-ball.md)
- [The track map on Euclidean space](maps/track-map-euclid.md)
- [The completed map on Euclidean space](maps/completed-map-euclid.md)
- [Completed cutoff](maps/completed-cutoff.md)
- [Representatives of the finite quotients](../../local-data/control/representative-map.md)
- [Completed map](completed-map.md)
- [The lift](../torus/lift.md)
- [The quotient Euclidean metric](../torus/dist2.md)
- [Modulus of the track family](modulus.md), [track maps](track-map.md)
- [Torus test map](torus-test-map.md)
- [The torus](../grid/torus.md)
- [Local datum](../../local-data/chart/local-datum.md), [round sphere](../../corner/round-sphere.md)
## Proof depends on
- [The quotient map](../torus/proj.md)
- [The quotient map inverts the lift](../torus/proj-lift.md)
- [Continuity of the lift](../torus/continuous-lift.md)
- [The torus norm and the Euclidean norm of the lift](../torus/norm-le-norm-lift.md)
- [The lift inverts the quotient map near the origin](../torus/lift-proj.md)
- [The quotient map does not increase distances](../torus/dist2-proj-le.md)
- [Continuity of the quotient map](../torus/continuous-proj.md)
- [Test map invariant](../../local-data/chart/test-map-invariant.md), [test map continuous](../../local-data/chart/test-map-continuous.md), [averaged map displacement](../../local-data/chart/averaged-map-displacement.md), [representatives](../../local-data/control/representatives.md)

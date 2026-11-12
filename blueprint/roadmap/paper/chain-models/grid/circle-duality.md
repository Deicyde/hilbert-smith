---
article_id: af_c2c4733f486398f482f90979
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.circle_duality
---

# Circle duality

Let $k\in\mathbb N$; for $k=0$ every object is zero and the bound $h/2$ in (5) is read as $0$. On $S=S_k$, use the [dual complex](../../l-theory/base/complexes/dual-complex.md) $S^{1-*}$, whose differential $d_r=(-1)^rd^*$ is written $d$, and the [involution](../../l-theory/base/complexes/structure-involution.md) $(T\psi)_r=(-1)^{r(1-r)}\psi_{1-r}^*$ on the [structure complex](../../l-theory/base/complexes/structure-complex.md) $M(S)$. Define $\varphi\in M(S)_1$ and $H\in M(S)_2$ by
$$\varphi([w]^*)=e_{w-1},\quad\varphi(e_w^*)=[w],\qquad H(e_w^*)=e_w,\ H([w]^*)=0,$$
and put $\varphi^{s}=\varphi+\tfrac12\partial H$. Here $\partial H=dH+Hd$. Then:

1. $\partial\varphi=0$, and $\varphi:S^{1-*}\to S$ is a chain isomorphism with inverse $b$ given by $b(e_w)=[w+1]^*$ and $b([w])=e_w^*$;
2. $T\varphi=\varphi+\partial H$, so that $\varphi^s=\tfrac12(\varphi+T\varphi)$, $\partial\varphi^s=0$ and $T\varphi^s=\varphi^s$;
3. $\varphi^sb-1=dK+Kd$ and $b\varphi^s-1=dK'+K'd$, where $K=\tfrac12Hb$ and $K'=\tfrac12bH$;
4. $\varepsilon\varphi^s(e_w^*)=1=e_w^*(\sum_ve_v)$;
5. with every [cell](cubical/circle-cell.md) and its dual [labelled](cubical/circle-label.md) at the cell's center in $\mathbb R/4\mathbb Z$ ($[w]$ at $4w/k$, $e_w$ at $(4w+2)/k$), every component of $\varphi,\varphi^s,b,H,K,K'$ has [propagation](../../categories/asymptotic/propagation.md) at most $h/2$.

*Proof sketch.* Direct computation. Write $\sigma$ for the shift $[w]\mapsto[w+1]$ of $\mathbb Q^k$; then $d=\sigma-1$, $d^*=\sigma^{-1}-1$, $\varphi_{0,1}=1$, $\varphi_{1,0}=\sigma^{-1}$, $b_0=1$, $b_1=\sigma$, and components in other degrees live on zero objects. (1) $d\varphi([w]^*)=[w]-[w-1]$, and $d[w]^*=-d^*[w]^*=e_w^*-e_{w-1}^*$, so $\varphi(d[w]^*)=[w]-[w-1]$. (2) $T\varphi$ sends $[w]^*\mapsto e_w$ and $e_w^*\mapsto[w+1]$. The difference $T\varphi-\varphi$ is $[w]^*\mapsto e_w-e_{w-1}=Hd[w]^*$ and $e_w^*\mapsto[w+1]-[w]=dHe_w^*$. Then $T\partial=\partial T$ and $T^2=1$ give the rest. (3) $\varphi^sb=1+\tfrac12(dH+Hd)b$, and $b$ is a chain map; likewise for $b\varphi^s$. (4) $\varphi^s(e_w^*)=\tfrac12([w]+[w+1])$. (5) Read off the formulas.

## Sources

- New: $\varphi$ is slant with the Serre diagonal $\Delta e_w=[w]\otimes e_w+e_w\otimes[w+1]$, and $\varphi^s$ is its symmetrization over $\mathbb Q$. This replaces the dual-block comparison of HS paper, Section 7.

## Depends on

- [Labels of the circle cells](cubical/circle-label.md)
- [The circle complex](cubical/circle-complex.md)
- [The cell of a basis vector of the circle complex](cubical/circle-cell.md)
- [Augmentation of the circle complex](cubical/circle-aug.md)
- [Fundamental chain of the circle complex](cubical/circle-fundamental.md)
- [circle duality data](poincare/circle-data/circle-phi.md), [circle homotopy element](poincare/circle-data/circle-h.md), [symmetric circle structure](poincare/circle-data/circle-phi-sym.md), [circle inverse](poincare/circle-data/circle-b.md), [circle homotopy](poincare/circle-data/circle-k.md), [dual circle homotopy](poincare/circle-data/circle-k-dual.md)
- [Dual complex](../../l-theory/base/complexes/dual-complex.md), [structure complex](../../l-theory/base/complexes/structure-complex.md), [the involution T](../../l-theory/base/complexes/structure-involution.md), [propagation](../../categories/asymptotic/propagation.md)
- [The shift of a complex](../../l-theory/base/complexes/shift.md)

## Proof depends on

- [T is an involution](../../l-theory/base/complexes/structure-involution-square.md)

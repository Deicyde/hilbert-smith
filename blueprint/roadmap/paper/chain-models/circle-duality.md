---
declaration: lemma
origin: bridged
---

# Circle duality

On $S=S_k$, use the shifted dual $S^{1-*}$ with differential $\delta_r=(-1)^rd^*$, and the transpose $(T\psi)_r=(-1)^{r(1-r)}\psi_{1-r}^*$. Define
$$\varphi([w]^*)=e_{w-1},\quad\varphi(e_w^*)=[w],\qquad H(e_w^*)=e_w,\ H([w]^*)=0,$$
and put $\varphi^{s}=\varphi+\tfrac12(dH+H\delta)$. Then:

1. $\varphi$ is a chain isomorphism, with inverse $b$ given by $b(e_w)=[w+1]^*$ and $b([w])=e_w^*$;
2. $T\varphi=\varphi+dH+H\delta$, so that $\varphi^s=\tfrac12(\varphi+T\varphi)$ and $T\varphi^s=\varphi^s$;
3. $\varphi^sb-1=d K+Kd$ and $b\varphi^s-1=\delta K'+K'\delta$, where $K=\tfrac12Hb$ and $K'=\tfrac12bH$;
4. $\varepsilon\varphi^s(e_w^*)=1=e_w^*(\sum_ve_v)$;
5. with cells labeled at their centers, $\varphi,\varphi^s,b,H,K,K'$ have propagation at most $h/2$.

*Proof sketch.* Direct computation. $d\varphi[w]^*=[w]-[w-1]=\varphi\delta[w]^*$. The map $T\varphi$ sends $[w]^*\mapsto e_w$ and $e_w^*\mapsto[w+1]$, which differs from $\varphi$ by $dH+H\delta$. Item 3 follows because $b$ is a chain map. Item 5 is read off the formulas.

## Sources

- New: $\varphi$ is slant with the Serre diagonal $\Delta e_w=[w]\otimes e_w+e_w\otimes[w+1]$, and $\varphi^s$ is its symmetrization over $\mathbb Q$. This replaces the dual-block comparison of HS paper, Section 7.

## Depends on

- [Cubical torus grid](cubical-torus-grid.md)

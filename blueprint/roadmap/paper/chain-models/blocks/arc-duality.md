---
article_id: af_ea2a080113bfc55e94567824
declaration: lemma
origin: background
---
# Arc duality

With $\delta_r=(-1)^rd^*$ on $I_m^{1-*}$:
1. $T\varphi_I=\varphi_I$ and $d\varphi_I-\varphi_I\delta=j\varphi_Cj^*$;
2. $\varphi_I$ restricts to a chain map $\Psi:R\to I_m$;
3. $b$ is a chain map, $\Psi b-1=dK_1+K_1d$ and $b\Psi-1=\delta K_2+K_2\delta$;
4. with cells labeled at their centres, all these maps have propagation at most the mesh.

*Proof sketch.* Write $\varphi$ for the unsymmetrized map $e_w^*\mapsto[w]$, $[w]^*\mapsto e_{w-1}$. Then $\varphi_I=\varphi+\tfrac12(dH+H\delta)$. A direct check gives $d\varphi-\varphi\delta=j\varphi_Cj^*$; the defect sits at $[0]^*$ and $[m]^*$. The correction is a boundary, so it does not change the defect. Item 2 holds because $j^*$ kills $R$. On $R$, $\varphi$ includes a copy of $I_{m-1}$, and $b$ retracts onto it: $b\varphi=1$ and $\varphi b-1=dK+Kd$. Add the corrections $\tfrac12Hb$ and $\tfrac12bH$, using that $b$ is a chain map.

## Sources
- New. Replaces the cone-section argument of HS paper, Section 12.
## Depends on
- [Arc pair](arc-pair.md)

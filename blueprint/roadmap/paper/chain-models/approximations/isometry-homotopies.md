---
article_id: af_90a5b0f9a0f674bee9fee189
declaration: theorem
origin: bridged
---
# Isometry homotopies

Put $s_i=3\omega(2h_i)+8h_i$. There are $U_g=U^T_g\otimes\varphi_P$ with $a_g\varphi_ia_g^*-\varphi_i=dU_g+U_g\delta$ and torus propagation at most $s_i+2h_i$. Hence for $0<v<v'$, eventually $U_g^{[v,v']}$ has graph type $\chi_i(0)$ with bound $\to0$.

*Proof sketch.* On $C^{n-*}$ take $\Gamma(c^*)=\mathrm{Box}(N_{s_i}(\operatorname{st}c))$. It is nested under cofaces, because $\operatorname{st}e\subseteq\operatorname{st}c$ for $e\supseteq c$. An entry of $a^*$ at $c^*$ picks $e$ with $c\in\Gamma_{\hat g}(e)$, $\varphi^s$ stays in $\operatorname{st}e$, and $a$ lands within $s_i$ of $|c|$. In degree $0$, $\varepsilon a\varphi a^*(\alpha)=\alpha(az)=\alpha(z)=\varepsilon\varphi(\alpha)$. Apply carried homotopies and tensor with $\varphi_P$. Then use $f_T$ and $\pi$ continuity.

## Sources
- HS paper, Section 9.
## Depends on
- [Poincaré](../grid/chain-model-poincare.md), [group approximations](group-approx.md)
## Proof depends on
- [Carried homotopies](../grid/carried-homotopy.md), [fundamental cycle](fundamental-cycle-fixed.md), [buffered restriction](buffered-restriction.md)

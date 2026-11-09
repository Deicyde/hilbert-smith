---
declaration: def
origin: background
---
# Block pair

A *block* is $Q=F_1\otimes\dots\otimes F_\ell\otimes P$, where each factor $F_j$ is either a circle $S_k$ or an arc $I_m$ (any mesh). Its dimension is $N_Q=\ell+4$. The boundary $\partial Q$ is spanned by the cells having an endpoint vertex in some arc factor, and $j:\partial Q\to Q$ is the inclusion. Put $\varphi_Q=\bigotimes_j\varphi_{F_j}\otimes\varphi_P$, using $\varphi^s$ for circles and $\varphi_I$ for arcs. Put $b_Q=\bigotimes_jb_{F_j}\otimes b_P$, and
$$\varphi_{\partial Q}=\sum_{F_j\text{ arc}}\bigl(\varphi_{F_1}\otimes\cdots\otimes\varphi_{C_j}\otimes\cdots\otimes\varphi_P\bigr)\rho_j,$$
where $\rho_j$ restricts a cochain of $\partial Q$ to the face with $j$-th factor $C_j$. Everything uses Koszul signs. The fundamental chain is $z_Q=\pm\bigotimes_j(\sum_we_w)\otimes e_4$, with the sign of the [chain model](chain-model.md).

## Sources
- New.
## Depends on
- [Arc pair](arc-pair.md), [chain-model duality](chain-model-duality.md)

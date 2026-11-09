---
declaration: def
origin: bridged
---

# The forgetful functor on tails

Write $\mathcal P_{\mathbf G},\mathcal V_{\mathbf G}$ for the groups $G_i$ and $\mathcal P_{\mathbf 1},\mathcal V_{\mathbf 1}$ for trivial groups. $U:\mathcal P_{\mathbf G}\to\mathcal P_{\mathbf 1}$ applies $U_{G_i}$ in coordinate $i$. $\bar U:\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf 1}$ is $U$ on objects and $[u]\mapsto[Uu]$ on morphisms, so that $\bar U\circ q=q\circ U$ and $\pi_iU=U_{G_i}\pi_i$ hold strictly.

*Proof sketch.* (Well-definedness.) $U$ maps objects of $\mathcal S$ to objects of $\mathcal S$, so it maps maps that factor through $\mathcal S$ to maps that factor through $\mathcal S$. Both functors commute strictly with transposition.

## Sources

- HS paper, Section 3

## Depends on

- [Forget functor](forget-functor.md)
- [Tail category](tail-category.md)

---
article_id: af_449f621470b7dc3947a40555
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.ChainModels.Torus.norm_ofLp_lift
---

# The maximum norm of the lift

For $x\in\mathbb T^n$, $|\tilde x|_\infty=d_\infty(x,0)$, where $|\cdot|_\infty$ is the maximum norm on $\mathbb R^n$.

*Proof sketch.* The lift lies in $[-2,2)^n$, where each coordinate is at most half the period from $0$, so $|\tilde x_j|=d(x_j,0)$ for each $j$, using $q(\tilde x)=x$; take the maximum over $j$.

## Sources

- New: the torus closing of the chart cube $[-2,2]^n$.

## Depends on

- [The lift](lift.md)
- [The torus](../grid/torus.md)

## Proof depends on

- [The quotient map inverts the lift](proj-lift.md)
- [The quotient map](proj.md)

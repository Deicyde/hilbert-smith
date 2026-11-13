---
article_id: af_770ce385c46d2bd2dd308f3f
declaration: def
origin: background
statement: formalized
lean: HSP.Evaluation.cubicalPinch
---
# Cubical pinch

Let $n\in\mathbb N$ and $s>0$, and put $a=1/4$ and $b=1/2$. For $\tilde x\in\mathbb R^n$ put
$$c_\kappa(\tilde x)=\tfrac as\min\Bigl(1,\tfrac{b-|\tilde x|_\infty}{b-a}\Bigr).$$
The *cubical pinch* is the continuous map $\kappa:\mathbb T^n\to S^n$, $\mathbb T^n=(\mathbb R/4\mathbb Z)^n$, given for $x$ with [lift](../chain-models/torus/lift.md) $\tilde x\in[-2,2)^n$ (the [torus](../chain-models/grid/torus.md)) by $\kappa(x)=\tilde x/c_\kappa(\tilde x)$ if $c_\kappa(\tilde x)>0$, and $\kappa(x)=\infty$ otherwise.

*Proof sketch.* (Continuity.)
1. $x\mapsto|\tilde x|_\infty$ is continuous on $\mathbb T^n$, since $|\tilde x|_\infty=d_\infty(x,0)$ ([maximum norm of the lift](../chain-models/torus/norm-lift.md)); hence $x\mapsto c_\kappa(\tilde x)$ is continuous, $c_\kappa(\tilde x)>0$ exactly when $|\tilde x|_\infty<b$, and $c_\kappa\le a/s$.
2. On the open set $\{|\tilde x|_\infty<b\}$, which lifts homeomorphically into $(-2,2)^n$, $\kappa$ is a quotient of continuous functions with positive denominator.
3. Let $c_\kappa(\tilde x_0)\le0$, so $|\tilde x_0|_\infty\ge b$. As $x\to x_0$, $|\tilde x|_\infty\to|\tilde x_0|_\infty$ and $c_\kappa(\tilde x)\to c_\kappa(\tilde x_0)\le0$, so wherever $\kappa(x)$ is finite, $|\kappa(x)|\ge|\tilde x|_\infty/c_\kappa(\tilde x)\to\infty$. So $\kappa(x)\to\infty=\kappa(x_0)$, as for the pinch.

## Sources
- New.
## Depends on

- [The torus](../chain-models/grid/torus.md)

## Proof depends on

- [The maximum norm of the lift](../chain-models/torus/norm-lift.md)
- [Continuity of the lift](../chain-models/torus/continuous-lift.md)
- [The torus norm and the Euclidean norm of the lift](../chain-models/torus/norm-le-norm-lift.md)
- [The lift](../chain-models/torus/lift.md)

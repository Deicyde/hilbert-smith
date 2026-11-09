---
article_id: af_c79595557db064ad43eb7479
declaration: lemma
origin: bridged
---
# Carried homotopies

Let $u,v:E\to F$ be chain maps carried by $\Gamma$ that agree on a based subcomplex $E'$, with $\varepsilon u=\varepsilon v$ on $E_0$. Then there is a carried $H$ of degree $+1$ with $u-v=dH+Hd$ and $H|_{E'}=0$. Under the label hypothesis of [carried chain maps](carried-chain-map.md), $\operatorname{prop}(H)\le a$.

*Proof sketch.* Set $H=0$ on $E'$ and induct on degree. The residual $u(e)-v(e)-H(de)$ is a cycle in $\Gamma(e)$, and in degree $0$ its augmentation is $0$. Fill it.

## Sources
- HS paper, Section 7.
## Depends on
- [Carriers](acyclic-carriers.md)

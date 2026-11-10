---
article_id: af_c79595557db064ad43eb7479
declaration: lemma
origin: bridged
---
# Carried homotopies

Let $u,v:E\to F$ be chain maps carried by $\Gamma$ that agree on a based subcomplex $E'$, with $\varepsilon u=\varepsilon v$ on $E_0$. Then there is a carried $H$ of degree $+1$ with $u-v=dH+Hd$ and $H|_{E'}=0$. Under the label hypothesis of [carried chain maps](carried-chain-map.md), $\operatorname{prop}(H)\le a$.

*Proof sketch.* Build $H$ on basis elements $e\notin E'$ in order of increasing degree $r$, with $H=0$ on $E'$. The target value is a primitive of $w(e)=u(e)-v(e)-H(de)$. Nesting of the carrier puts $w(e)$ in $\Gamma(e)$. The identity already arranged in degree $r-1$ gives $dw(e)=0$, and for $r=0$, where $H(de)=0$, $\varepsilon w(e)=0$ because $\varepsilon u=\varepsilon v$. Since $\Gamma(e)$ is augmented acyclic, $w(e)=dy$ for some $y\in\Gamma(e)_{r+1}$; set $H(e)=y$. Then $u-v=dH+Hd$ on $e$, and $H$ is carried, which gives the propagation bound.

## Sources
- HS paper, Section 7 (carrier lemma).
## Depends on
- [Carriers](acyclic-carriers.md)

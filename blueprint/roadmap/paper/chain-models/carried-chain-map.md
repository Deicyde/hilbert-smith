---
declaration: lemma
origin: cited
---
# Carried chain maps

Let $\Gamma$ be a carrier from $E$ to $F$, and let $\varepsilon_E:E_0\to\mathbb Q$ satisfy $\varepsilon_Ed_1=0$. Let $E'\subseteq E$ be a based subcomplex and $u':E'\to F$ a carried chain map with $\varepsilon u'=\varepsilon_E$ on $E'_0$. Then there is a carried chain map $u:E\to F$ with $u|_{E'}=u'$ and $\varepsilon u=\varepsilon_E$. If every label of $\Gamma(e)$ is within $a$ of the label of $e$, then $\operatorname{prop}(u)\le a$.

*Proof sketch.* Induct on degree, keeping $u'$ on $E'$. For a degree-$0$ basis element $e\notin E'$, choose $u(e)\in\Gamma(e)_0$ with $\varepsilon u(e)=\varepsilon_E(e)$; $\varepsilon$ is onto because $\Gamma(e)$ is augmented acyclic. In degree $r\ge1$, $u(de)$ lies in $\Gamma(e)$ and is a cycle. For $r=1$ its augmentation is $\varepsilon_E(de)=0$; this step needs $\varepsilon u'=\varepsilon_E$ on $E'$. Fill the cycle in $\Gamma(e)$. The propagation bound holds because each $u(e)$ lies in $\Gamma(e)$.

## Sources
- HS paper, Section 7 (carrier lemma). New: the relative clause, with the augmentation hypothesis.
## Depends on
- [Carriers](acyclic-carriers.md)
- [Propagation](../categories/propagation.md)

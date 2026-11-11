---
article_id: af_b76fff5a13f5b64733765ba7
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.supp_inter
---

# Support intersection

Let $X$ be compact and let $A,B\subset X$ be closed (neither invariance nor isometry of the action is needed). An object lies in both $\mathcal A_A$ and $\mathcal A_B$ if and only if it lies in $\mathcal A_{A\cap B}$.

*Proof sketch.* By compactness of $X$, for every $\varepsilon>0$ there is $\delta>0$ such that the $\delta$-thickenings of $A$ and $B$ meet inside the $\varepsilon$-thickening of $A\cap B$. The sets $\overline{N_{1/m}}A\cap\overline{N_{1/m}}B\setminus N_\varepsilon(A\cap B)$ are decreasing and compact with empty intersection. The converse inclusion is monotonicity of thickening.

## Sources

- HS paper, Section 2

## Depends on

- [Support subcategory](support-subcategory.md)

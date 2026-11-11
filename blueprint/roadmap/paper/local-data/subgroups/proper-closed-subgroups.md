---
article_id: af_3f6d5fcef6452da01ae2f1f7
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.le_padicSubgroup_one_of_ne_top
---

# Proper closed subgroups lie in $p\mathbb Z_p$

Every closed additive subgroup $K\neq\mathbb Z_p$ of $\mathbb Z_p$ is contained in $H_1$.

*Proof sketch.* If $K=0$ there is nothing to prove. Otherwise $K=H_j$ by the classification of closed subgroups, and $j\ge1$ because $K\ne H_0$. Hence $K\subseteq H_1$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)
- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 409-411 (a similar use of the classification)

## Depends on

- [The subgroups $H_j$](padic-subgroups.md)

## Proof depends on

- [Closed subgroups of $\mathbb Z_p$](closed-subgroups.md)

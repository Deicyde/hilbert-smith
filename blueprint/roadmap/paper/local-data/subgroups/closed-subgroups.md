---
article_id: af_da8fa0450d914844945f7147
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: HSP.closed_eq_padicSubgroup
---

# Closed subgroups of $\mathbb Z_p$

Every closed additive subgroup $K\neq 0$ of $\mathbb Z_p$ equals $H_j$ for some $j\in\mathbb N$.

*Proof sketch.* Integers are dense in $\mathbb Z_p$, so the closed subgroup $K$ is closed under multiplication by $\mathbb Z_p$, that is, $K$ is a nonzero ideal. Every nonzero ideal of $\mathbb Z_p$ is some $H_j$: pick a nonzero $x\in K$ of minimal valuation $j$ and write $x=up^j$ with $u$ a unit. Then $p^j=u^{-1}x\in K$, so $H_j\subseteq K$. Minimality of $j$ gives $K\subseteq H_j$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 61-64
- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The subgroups $H_j$](padic-subgroups.md)

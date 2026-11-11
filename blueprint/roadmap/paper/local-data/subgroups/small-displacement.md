---
article_id: af_4d0d6c4f0685747934c42180
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.exists_nhds_one_small_displacement
---

# Uniformly small displacement near the identity

Let a group $G$ with a topology (no continuity of the group operations is needed) act jointly continuously on a topological space $M$. Let $e$ be an open partial homeomorphism from $M$ to $\mathbb R^n$, that is, a homeomorphism from an open subset of $M$ (the domain of $e$) onto an open subset of $\mathbb R^n$. Let $C$ be a compact subset of the domain of $e$, and let $\delta>0$. Then there is a neighbourhood $V$ of the identity in $G$ such that for all $g\in V$ and $x\in C$, the point $gx$ lies in the domain of $e$ and $|e(gx)-e(x)|<\delta$.

*Proof sketch.* Let $S$ be the set of pairs $(g,x)\in G\times M$ with $x$ and $gx$ in the domain of $e$ and $|e(gx)-e(x)|<\delta$. The pairs with $x$ and $gx$ in the domain form an open set, because the domain is open and the action is continuous; on it $(g,x)\mapsto e(gx)-e(x)$ is continuous, so $S$ is open. It contains $\{1\}\times C$, because $C$ lies in the domain. The tube lemma, for the compact sets $\{1\}$ and $C$, gives an open $V\ni 1$ with $V\times C\subseteq S$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)
- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 51-54

## Depends on

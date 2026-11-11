---
article_id: af_360a5e321d9b3a5fff62b330
declaration: lemma
origin: background
---

# The subgroups $H_j$ form a basis at $0$

Each $H_j$ is open and compact in $\mathbb Z_p$, $H_{j+1}\subseteq H_j$ for every $j$, and every neighbourhood of $0$ in $\mathbb Z_p$ contains some $H_j$.

*Proof sketch.* $H_j$ is the closed ball of radius $p^{-j}$ about $0$ for the $p$-adic norm, which is also the open ball of radius $p^{-j+1}$, since the norm takes values in $\{0\}\cup p^{\mathbb Z}$. Closed balls in $\mathbb Z_p$ are compact because $\mathbb Z_p$ is compact. The radii decrease to $0$, so the balls are nested and form a neighbourhood base.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 33-37

## Depends on

- [The subgroups $H_j$](padic-subgroups.md)

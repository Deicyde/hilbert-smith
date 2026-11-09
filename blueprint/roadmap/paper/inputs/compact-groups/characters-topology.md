---
article_id: af_e679f715ef799000cb0c9c7c
declaration: lemma
origin: background
not_ready: true
---

# Characters determine the topology

Let $A$ be a compact Hausdorff commutative topological group and $X$ a topological space. A map $f\colon X\to A$ is continuous if $\chi\circ f$ is continuous for every character $\chi$ of $A$.

*Proof sketch.* The map $A\to\prod_{\chi}\mathbb T$ sending $a$ to $(\chi(a))_\chi$ is continuous, and it is injective because characters separate points. A continuous injection from a compact space to a Hausdorff space is a closed embedding, so continuity into $A$ is continuity of each coordinate.

## Sources

- New: the compact-to-Hausdorff embedding

## Depends on

## Proof depends on

- [Characters separate points](characters-separate.md)

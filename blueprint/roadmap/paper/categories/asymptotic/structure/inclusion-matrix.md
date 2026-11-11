---
article_id: af_536c8ef60e9d37c0c420cf5a
declaration: def
origin: bridged
statement: formalized
lean: HSP.FreeCat.inclMat
---

# The inclusion matrix

Let $G$ be a finite group and $e:\{1..m\}\to\{1..m'\}$ a map. The *inclusion matrix* of $e$ is the rational matrix with rows indexed by $G\times\{1..m'\}$ and columns by $G\times\{1..m\}$ whose entry at $(a,b)$ is $1$ if $a=(g,e(k))$ for $b=(g,k)$, and $0$ otherwise. For injective $e$ it is the matrix of the inclusion of the basis $G\times\{1..m\}$ into $G\times\{1..m'\}$ along $e$, and its transpose is the matrix of the corresponding projection; these give the coordinate inclusions and projections of sums.

## Sources

- HS paper, Section 3

## Depends on

- [Free category of a finite group](../free-category.md)

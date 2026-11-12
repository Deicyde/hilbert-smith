---
article_id: af_38f8013b8d0ead74ad03ed82
declaration: def
origin: bridged
statement: formalized
lean: HSP.groupEnum
---

# The group enumeration

For a finite group $G$ fix the bijection $\varepsilon_G:G\to\{0..|G|-1\}$. The group enumeration is the bijection $e^G_n:G\times\{1..n\}\to\{1..|G|\,n\}$, $e^G_n(g,k)=\varepsilon_G(g)\,n+k$, from the basis of the object $n$ of the [free category](../asymptotic/free-category.md) to $\{1..|G|\,n\}$. Only the finiteness of $G$ is used, not its group structure.

## Sources

- HS paper, Section 2

## Depends on

- [Free category of a finite group](../asymptotic/free-category.md)

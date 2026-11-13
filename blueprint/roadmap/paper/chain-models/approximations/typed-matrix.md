---
article_id: af_755e12206f867077b64651a8
declaration: structure
origin: bridged
statement: formalized
lean: HSP.ChainModels.TypedMatrix, HSP.ChainModels.TypedMatrix.of
---

# Typed labelled matrices

Let $n,p\in\mathbb N$. A *typed labelled matrix* consists of
- finite sets $B$ (the source cells) and $B'$ (the target cells);
- torus labels $x_b\in\mathbb T^n$ for $b\in B$ and $x'_{b'}\in\mathbb T^n$ for $b'\in B'$, in the [torus](../grid/torus.md);
- a rational matrix $u\in\mathbb Q^{B'\times B}$, read as a map $u:\mathbb Q^B\to\mathbb Q^{B'}$;
- a type $c\in C_p=\mathbb Z/p$.

For finite sets $B,B'$, labels $x,x'$, a matrix $u$ and $c\in C_p$, write $(u,x,x';c)$ for the typed labelled matrix with these data.

## Sources

- New: the format of the matrices controlled in the chain-model estimates (HS paper, Section 9).

## Depends on

- [The torus](../grid/torus.md)

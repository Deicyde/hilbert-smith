---
declaration: lemma
origin: bridged
---

# Invariant Lagrangians kill the signature

Let $L\subset W$ be a $G$-invariant subspace with $b|_{L\times L}=0$ and $2\dim L=\dim W$. Then $\mathrm{sign}_b(g)=0$ for every $g$.

*Proof sketch.* Take a splitting. $L\cap V^\pm=0$ because $L$ is isotropic and $V^\pm$ is definite. So $\dim V^\pm\le\dim L$. Since $\dim V^++\dim V^-=2\dim L$, both are equalities. Hence $W=L\oplus V^+=L\oplus V^-$, and the quotient map gives $G$-isomorphisms $V^+\cong W/L\cong V^-$. The two traces are therefore equal.

## Sources

- HS paper, Section 3
- OpenAI preprint, 04-lattice.tex lines 55-60 (the non-equivariant form of the statement)
- New: the quotient isomorphism replaces the HS paper's construction of a Lagrangian complement.

## Depends on

- [Independence](signature-splitting-independence.md)

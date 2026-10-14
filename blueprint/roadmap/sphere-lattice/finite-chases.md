---
article_id: af_816166160854d60d699adae3
declaration: lemma
origin: cited
lean: HilbertSmith.fiveTermChase HilbertSmith.squareChase
statement: formalized
proof: formalized
---

# Finite diagram chases

In a commutative diagram of exact rows
$A_1 \to \cdots \to A_5$ over $B_1 \to \cdots \to B_5$, if the
kernels and cokernels of $f_1, f_2, f_4, f_5$ are annihilated by
$q$, then those of $f_3$ are annihilated by $q^3$. In a commutative
square with both horizontal kernels and cokernels annihilated by
$2$, if those of $f$ are annihilated by $q$, then those of $g$ are
annihilated by $4q$ (the cokernel even by $2q$).

*Proof sketch.* Two elementary diagram chases: lift through exact
rows, clearing denominators at each of the three bounded stages
for the five-term chase, and through the square for the second.

The kernel bound for $f_1$ is unused by the chase and is kept to
match the source's symmetric statement. The cokernel bound for
$f_5$ is likewise unused and kept for the same reason. In the
square, the kernel bound for $i$ is unused and kept for the same
reason.

## Sources

- [Preprint source map: `lat:finite-chases`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

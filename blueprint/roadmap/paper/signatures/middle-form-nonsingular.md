---
declaration: lemma
origin: bridged
---

# The middle form is nonsingular, symmetric and invariant

$b_C$ is nondegenerate and symmetric, and $G$ acts by $b_C$-isometries.

*Proof sketch.* The structure is strictly symmetric, $T\varphi=\varphi$. In degree 2 this says $\varphi_2=(-1)^{2\cdot2}\varphi_2^T=\varphi_2^T$, which gives symmetry. The chain map $\varphi:C^{4-*}\to C$ is a homotopy equivalence, so $\varphi_2:H^2(C;\mathbb R)\to H_2(C;\mathbb R)$ is an isomorphism ([invariance](real-homology-invariance.md)). Nondegeneracy then follows from [the perfect pairing](real-evaluation-pairing.md). Invariance holds because $\varphi_2$ is equivariant and permutation matrices are orthogonal.

## Sources

- HS paper, Section 3
- [published: Ranicki 1980 Part I, Prop. 3.1] [U]

## Depends on

- [The middle form](middle-form.md)

## Proof depends on

- [Real homology is homotopy invariant](real-homology-invariance.md)
- [Evaluation is a perfect pairing](real-evaluation-pairing.md)

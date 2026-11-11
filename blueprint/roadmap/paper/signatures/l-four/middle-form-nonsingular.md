---
article_id: af_e40f7bb75496ea911cd28837
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.middleForm_nonsingular
---

# The middle form is nonsingular, symmetric and invariant

For a strict 4-dimensional symmetric Poincaré complex $(C,\varphi)$ in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$, $b_C$ is nondegenerate and symmetric, and $G$ acts by $b_C$-isometries.

*Proof sketch.* The structure is strictly symmetric, $T\varphi=\varphi$. In degree 2 this says $\varphi_2=(-1)^{2\cdot2}\varphi_2^T=\varphi_2^T$, which gives symmetry. The chain map $\varphi_\natural:C^{4-*}\to C$ is a homotopy equivalence, so it induces an isomorphism $H_2(C^{4-*};\mathbb R)\to H_2(C;\mathbb R)$ ([invariance](real-homology-invariance.md)). In degree 2 the [dual complex](../../l-theory/base/complexes/dual-complex.md) $C^{4-*}$ has the term $C_2^*$ and differentials $\pm d^T$, so $H_2(C^{4-*};\mathbb R)=H^2(C;\mathbb R)$, and the isomorphism is $[y]\mapsto[\varphi_2y]$. Nondegeneracy then follows from [the perfect pairing](real-evaluation-pairing.md). Invariance holds because $\varphi_2$ is equivariant and permutation matrices are orthogonal.

## Sources

- HS paper, Section 3
- [Ranicki 1980 Part I, Prop. 3.1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [The middle form](middle-form.md)

## Proof depends on

- [Dual complex](../../l-theory/base/complexes/dual-complex.md)
- [Real homology is homotopy invariant](real-homology-invariance.md)
- [Evaluation is a perfect pairing](real-evaluation-pairing.md)

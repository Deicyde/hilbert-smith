---
article_id: af_479039fd868fecf1de23882d
declaration: theorem
origin: background
lean: HilbertSmith.Duality.IsInvolutive HilbertSmith.Duality.biduality_map HilbertSmith.Duality.transpose_transpose HilbertSmith.Duality.transpose_add HilbertSmith.Duality.transpose_zero HilbertSmith.map_comp_map HilbertSmith.Duality.transpose_orthSum
statement: formalized
proof: formalized
---

# Transpose involution and orthogonal sums

Let $C$ be an additive category with a duality $(D, \varpi)$ as in
[Symmetric forms and orthogonal sums](symmetric-forms.md). The duality
is involutive when dualized biduality cancels biduality: $D(\varpi_X)$
after $\varpi_{DX}$ is the identity for every $X$. For an involutive
duality, the transpose is involutive: transposing twice returns the
original morphism. The transpose is additive, and the transpose of an
orthogonal sum is the orthogonal sum of the transposes.

Cited wherever forms are transposed twice or across sums: the cone
averaging, neutrality, and doubling arguments all move transposes
through orthogonal sums.

*Proof sketch.* Transposing twice unfolds to
$\varpi \gg D^2\alpha \gg D\varpi$; naturality of $\varpi$ moves
$D^2\alpha$ past, and involution cancels the rest. Additivity is
additivity of $D$. For sums, $D$ preserves biproducts, so $D$ of the
biproduct map is the biproduct of the $D$ maps, and $\varpi$ is
natural.

## Sources

- [Background map: `Balmer2000` §1](../../sources/background.md)

## Depends on

- [Symmetric forms and orthogonal sums](symmetric-forms.md)

## Proof depends on

- [Symmetric forms and orthogonal sums](symmetric-forms.md)

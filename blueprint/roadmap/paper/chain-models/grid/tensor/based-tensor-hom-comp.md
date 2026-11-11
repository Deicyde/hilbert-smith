---
article_id: af_4503a5ced53df0ab2fccede4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedTensorHom_comp
---

# Composition of tensors of graded maps

Let $f_r:C_r\to C'_{r+d}$, $g_r:E_r\to E'_{r+e}$, $f'_r:C'_r\to C''_{r+d'}$, $g'_r:E'_r\to E''_{r+e'}$ be graded maps of complexes of based vector spaces, where $E,E',E''$ and $C'$ vanish in negative degrees. Then the [tensors of graded maps](based-tensor-hom.md) satisfy
$$(f'\otimes g')(f\otimes g)=(-1)^{e'd}\,(f'f)\otimes(g'g)$$
as maps $(C\otimes E)_r\to(C''\otimes E'')_{r+d+e+d'+e'}$, where $f'f$ and $g'g$ have degrees $d+d'$ and $e+e'$.

*Proof sketch.* Compare blocks ([maps are determined by their blocks](block-ext.md), [blocks of a composite](block-comp.md), [blocks of a tensor of graded maps](tensor-hom-blocks.md)). From the summand $C_p\boxtimes E_{r-p}$ the only intermediate summand is $C'_{p+d}\boxtimes E'_{r-p+e}$, and the signs multiply to $(-1)^{ep+e'(p+d)}=(-1)^{e'd}(-1)^{(e+e')p}$; the Kronecker factors combine by the [Kronecker product of composites](kron-composite.md) and [of identities](kron-transport.md). If that intermediate summand is outside the range of summands, then $p+d<0$ or $r-p+e<0$, so $C'_{p+d}=0$ or $E'_{r-p+e}=0$ and both sides vanish ([zero factors](kron-zero.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor of graded maps of based complexes](based-tensor-hom.md)

## Proof depends on

- [Maps between concatenations are determined by their blocks](block-ext.md)
- [Blocks of a composite](block-comp.md)
- [Blocks of a tensor of graded maps](tensor-hom-blocks.md)
- [Kronecker product of composites](kron-composite.md)
- [Kronecker product of identities](kron-transport.md)
- [Kronecker product with a zero factor](kron-zero.md)

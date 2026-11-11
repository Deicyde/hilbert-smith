---
article_id: af_a9da9240ff2f4c16466220a3
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.basedDualTensorHom
---

# Dual tensor of graded maps of based complexes

Let $C$ and $E$ be complexes of based vector spaces with $E$ vanishing in negative degrees, $m+m'=k$, and let $F_r:(C^{m-*})_r\to(C^{m-*})_{r+d}$ and $G_r:(E^{m'-*})_r\to(E^{m'-*})_{r+e}$ be graded maps of the [dual complexes](../../../l-theory/base/complexes/dual-complex.md). The map $\Xi^{-1}(F\otimes G)\Xi:((C\otimes E)^{k-*})_r\to((C\otimes E)^{k-*})_{r+d+e}$ of the dual of the [tensor product of based complexes](../based-complex-tensor.md) is the map whose block from the dual of $C_{m-a}\boxtimes E_{m'-b}$ to the dual of $C_{m-a-d}\boxtimes E_{m'-b-e}$ (with $a+b=r$) is $s(a+d,b+e)\,(-1)^{ea}\,s(a,b)\,F_a\boxtimes G_b$, where $s(a,b)=(-1)^{b(a+m)}$, all other blocks being zero.

## Sources

- New: explicit bases for the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)
- [Dual complex](../../../l-theory/base/complexes/dual-complex.md)

import Mathlib

/-!
# The inclusion matrix

For a finite group `G` and a map `e : Fin m → Fin m'`, the inclusion matrix of the bases
`G × Fin m → G × Fin m'` along `e`: the entry at `(a, b)` is `1` if `a = (b.1, e b.2)` and `0`
otherwise. For an injective `e` it is the matrix of the coordinate inclusion; it gives the
coordinate inclusions and (transposed) projections of the sums in the free and asymptotic
categories.

## Encoding

`FreeCat.inclMat e` (the declaration of the article) only needs decidable equality on `G`; that it
is equivariant is proved where it is used.
-/

namespace HSP.FreeCat

variable {G : Type} [DecidableEq G]

/-- The *inclusion matrix* of `G × Fin m` into `G × Fin m'` along `e : Fin m → Fin m'`, with rows
indexed by `G × Fin m'`: the entry at `(a, b)` is `1` if `a = (b.1, e b.2)` and `0` otherwise. -/
def inclMat {m m' : ℕ} (e : Fin m → Fin m') : Matrix (G × Fin m') (G × Fin m) ℚ :=
  fun a b => if a = (b.1, e b.2) then 1 else 0

end HSP.FreeCat

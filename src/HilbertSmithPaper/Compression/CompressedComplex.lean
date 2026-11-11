import Mathlib
import HilbertSmithPaper.Compression.StartIndex
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticCategory
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.LocalData.Control.ControlSpaceCompact
import HilbertSmithPaper.ChainModels.Grid.Model.ChainModelLabel

/-!
# Compressed complex

For fixed local data with control space `T` and start index `i₀`, the compressed complex `C` has,
in each degree, the object of `𝒜_𝟏(T × Sⁿ)` whose based module `C_i` is spanned by the retained
cells `Ret_i` of `D_i`, with the control labels `λ(b) = (π(x̃_b), s_b)`, for `i ≥ i₀`, and is zero
for `i < i₀`.

## Encoding

* `compressedDim F i r` is the rank of `C_i` in degree `r`: the number of retained cells of
  `(D_i)_r` for `i ≥ i₀`, else `0`. For `i ≥ i₀`, `compressedCell F hi r b` is the `b`-th retained
  cell, in increasing order (`Finset.orderEmbOfFin`); it lies in `𝓑_i(t')` by buffers (1)
  (`startIndex_spec`), so its control label `controlLabel` is defined.
* The object before the quotient (`AsymPre`) is private; `compressed F r` (the declaration of
  the article) is its class in `AsymCat (GroupSeq.trivial p) (T × Sⁿ)`, `T × Sⁿ` with
  the product metric and action.
* The rank of `C_i` is `(compressed F r).as.n i`, which is `compressedDim F i r` by definition.
* `pr_i`, `in_i` and `Q_i` are the retained projection (`retainedProj`).
-/

open CategoryTheory

namespace HSP.Compression

open HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

open Classical in
/-- The rank of `C_i` in degree `r`: `|Ret_i ∩ (D_i)_r|` for `i ≥ i₀`, and `0` for `i < i₀`. -/
noncomputable def compressedDim (F : FixedLocalData p n D ρplus) (i : ℕ) (r : ℤ) : ℕ :=
  if startIndex F ≤ i then (retainedCells F i r).card else 0

private lemma compressedDim_of_le (F : FixedLocalData p n D ρplus) {i : ℕ} (hi : startIndex F ≤ i)
    (r : ℤ) : compressedDim F i r = (retainedCells F i r).card := by
  simp [compressedDim, hi]

/-- The `b`-th retained cell of `(D_i)_r`, in increasing order, for `i ≥ i₀`. -/
noncomputable def compressedCell (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (b : Fin (compressedDim F i r)) :
    Fin ((chainModel F.toLocalDatum i).X r).dim :=
  (retainedCells F i r).orderEmbOfFin (compressedDim_of_le F hi r).symm b

private lemma compressedCell_buffered (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (b : Fin (compressedDim F i r)) :
    compressedCell F hi r b ∈
      bufferedCells F.toLocalDatum F.ρ (chainModelLabel F.toLocalDatum i r) ((F.t + F.u) / 2) :=
  ((startIndex_spec F).2 i hi).1.1 r _
    ((mem_retainedCells F i r _).1 (Finset.orderEmbOfFin_mem _ _ b))

/-- The control label `λ(b) = (π(x̃_b), s_b)` of the `b`-th retained cell, for `i ≥ i₀`. -/
private noncomputable def compressedLabel (F : FixedLocalData p n D ρplus) {i : ℕ}
    (hi : startIndex F ≤ i) (r : ℤ) (b : Fin (compressedDim F i r)) :
    F.T × Corner.RoundSphere n :=
  controlLabel F.toLocalDatum F.ρ_pos F.ρ_lt (chainModelLabel F.toLocalDatum i r) ((F.t + F.u) / 2)
    ⟨compressedCell F hi r b, compressedCell_buffered F hi r b⟩

open Classical in
/-- The degree-`r` part of the compressed complex, before the quotient. -/
private noncomputable def compressedPre (F : FixedLocalData p n D ρplus) (r : ℤ) :
    AsymPre (GroupSeq.trivial p) (F.T × Corner.RoundSphere n) where
  n i := compressedDim F i r
  x i b := if hi : startIndex F ≤ i then compressedLabel F hi r b else
    (Fin.cast (by simp [compressedDim, hi]) b : Fin 0).elim0

/-- The *compressed complex* in degree `r`: the object of `𝒜_𝟏(T × Sⁿ)` spanned at level `i` by
the retained cells of `(D_i)_r` with their control labels for `i ≥ i₀`, and zero for `i < i₀`. -/
noncomputable def compressed (F : FixedLocalData p n D ρplus) (r : ℤ) :
    AsymCat (GroupSeq.trivial p) (F.T × Corner.RoundSphere n) :=
  ⟨compressedPre F r⟩

end HSP.Compression

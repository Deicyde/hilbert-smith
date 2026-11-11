import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Maps.TrackFamily
import HilbertSmithPaper.ChainModels.Approximations.CompletedMap

/-!
# The track family contains the completed maps and the identity

Every completed map `â = L_{a,0,a,t}` and the identity `L_{0,0,0,t}` lie in `𝓕`.

## Encoding

`trackFamily_mem A` (the declaration of the article) is the conjunction of the two statements.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

private lemma completedMapEuclid_zero (A : LocalDatum p n D ρplus)
    (x : EuclideanSpace ℝ (Fin n)) : completedMapEuclid A 0 x = x := by
  unfold completedMapEuclid; split_ifs <;> simp

/-- `â = L_{a,0,a,t}`. -/
private lemma trackMap_self (A : LocalDatum p n D ρplus) (a : ℤ_[p]) (t : unitInterval) :
    trackMap A a 0 a t = completedMap A a := by
  funext x
  simp [trackMap, completedMap, trackMapEuclid, completedMapEuclid_zero, ← add_smul]

/-- `id = L_{0,0,0,t}`. -/
private lemma trackMap_zero (A : LocalDatum p n D ρplus) (t : unitInterval) :
    trackMap A 0 0 0 t = id := by
  funext x
  simp [trackMap, trackMapEuclid, completedMapEuclid_zero, ← add_smul]

/-- `𝓕` contains every completed map and the identity. -/
lemma trackFamily_mem (A : LocalDatum p n D ρplus) :
    (∀ a : ℤ_[p], completedMap A a ∈ trackFamily A) ∧ (id : Torus n → Torus n) ∈ trackFamily A :=
  ⟨fun a => ⟨(a, 0, a, 0), trackMap_self A a 0⟩, ⟨(0, 0, 0, 0), trackMap_zero A 0⟩⟩

end HSP.ChainModels

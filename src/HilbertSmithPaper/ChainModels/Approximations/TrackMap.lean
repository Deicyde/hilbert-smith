import Mathlib
import HilbertSmithPaper.ChainModels.Torus.Proj
import HilbertSmithPaper.ChainModels.Torus.ProjLift
import HilbertSmithPaper.ChainModels.Torus.Lift
import HilbertSmithPaper.ChainModels.Approximations.CompletedMap
import HilbertSmithPaper.ChainModels.Grid.Torus

/-!
# Track maps

For `a, b, c ∈ ℤ_p` and `t ∈ [0,1]`, the track map `L_{a,b,c,t} = (1-t) â b̂ + t ĉ` on `ℝⁿ`. It is
the identity off `B(0,3/2)`, so it induces the map `x ↦ q(L(x̃))` of the torus. The family `𝓕`
consists of all these torus maps; it contains every completed map `â = L_{a,0,a,t}` and the
identity `L_{0,0,0,t}`.

## Encoding

`trackMapEuclid` is `L` on `ℝⁿ`, `trackMap` (the declaration of the article) the induced map
of `𝕋ⁿ`, and `trackFamily` the set `𝓕` of torus maps. `t` ranges over `unitInterval`.
-/

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- The track map `L_{a,b,c,t} = (1-t) â b̂ + t ĉ` on `ℝⁿ`. -/
noncomputable def trackMapEuclid (A : LocalDatum p n D ρplus) (a b c : ℤ_[p]) (t : unitInterval)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (1 - (t : ℝ)) • completedMapEuclid A a (completedMapEuclid A b x) +
    (t : ℝ) • completedMapEuclid A c x

/-- The track map `L_{a,b,c,t}` of the torus: `x ↦ q(L_{a,b,c,t}(x̃))`. -/
noncomputable def trackMap (A : LocalDatum p n D ρplus) (a b c : ℤ_[p]) (t : unitInterval)
    (x : Torus n) : Torus n :=
  Torus.proj (trackMapEuclid A a b c t (Torus.lift x))

/-- The family `𝓕` of all track maps of the torus. -/
def trackFamily (A : LocalDatum p n D ρplus) : Set (Torus n → Torus n) :=
  Set.range fun q : ℤ_[p] × ℤ_[p] × ℤ_[p] × unitInterval => trackMap A q.1 q.2.1 q.2.2.1 q.2.2.2

/-- `L_{a,b,c,t}` is the identity off `B(0,3/2)`. -/
lemma trackMapEuclid_of_le (A : LocalDatum p n D ρplus) (a b c : ℤ_[p]) (t : unitInterval)
    {x : EuclideanSpace ℝ (Fin n)} (hx : 3 / 2 ≤ ‖x‖) : trackMapEuclid A a b c t x = x := by
  simp only [trackMapEuclid, completedMapEuclid_of_le A _ hx, ← add_smul, sub_add_cancel,
    one_smul]

private lemma completedMapEuclid_zero (A : LocalDatum p n D ρplus)
    (x : EuclideanSpace ℝ (Fin n)) : completedMapEuclid A 0 x = x := by
  unfold completedMapEuclid; split_ifs <;> simp

/-- `â = L_{a,0,a,t}`. -/
lemma trackMap_self (A : LocalDatum p n D ρplus) (a : ℤ_[p]) (t : unitInterval) :
    trackMap A a 0 a t = completedMap A a := by
  funext x
  simp [trackMap, completedMap, trackMapEuclid, completedMapEuclid_zero, ← add_smul]

/-- `id = L_{0,0,0,t}`. -/
lemma trackMap_zero (A : LocalDatum p n D ρplus) (t : unitInterval) :
    trackMap A 0 0 0 t = id := by
  funext x
  simp [trackMap, trackMapEuclid, completedMapEuclid_zero, ← add_smul]

/-- `𝓕` contains every completed map. -/
lemma completedMap_mem_trackFamily (A : LocalDatum p n D ρplus) (a : ℤ_[p]) :
    completedMap A a ∈ trackFamily A :=
  ⟨(a, 0, a, 0), trackMap_self A a 0⟩

/-- `𝓕` contains the identity. -/
lemma id_mem_trackFamily (A : LocalDatum p n D ρplus) : (id : Torus n → Torus n) ∈ trackFamily A :=
  ⟨(0, 0, 0, 0), trackMap_zero A 0⟩

end HSP.ChainModels

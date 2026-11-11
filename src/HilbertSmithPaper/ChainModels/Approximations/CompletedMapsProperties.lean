import Mathlib
import HilbertSmithPaper.ChainModels.Approximations.Modulus
import HilbertSmithPaper.ChainModels.Approximations.TrackMap
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.ChainModels.Grid.Torus
import HilbertSmithPaper.Corner.RoundSphere

/-!
# Properties of completed maps

Five properties of the track family `𝓕`, its modulus `ω`, the completed maps and the torus test
map, for a local datum and a pinch radius `0 < ρ < ρ₊`.

## Encoding

* "Off `B̄(0, r)`" on the torus means `|x̃| > r` for the lift `x̃`; "off `B(0, r)`" means `|x̃| ≥ r`.
* The modulus `ω_f` of item 4 is expressed as uniform continuity of `f_T` into `(Sⁿ, d_S)`.
* `β_i` of item 5 is `trackDefect A i`, the supremum over `g, h ∈ ℤ/p^i` and `x ∈ Ω` with
  `|x| ≤ 3/8` of `|r_i(g)·(r_i(h)·x) - r_i(g+h)·x|`; the points `L(x)` are taken in `ℝⁿ`.
-/

open Filter Topology OnePoint

namespace HSP.ChainModels

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- `β_i = sup {|r_i(g)·(r_i(h)·x) - r_i(g+h)·x| : g, h ∈ ℤ/p^i, |x| ≤ 3/8}`. -/
noncomputable def trackDefect (A : LocalDatum p n D ρplus) (i : ℕ) : ℝ :=
  sSup {δ | ∃ g h : ZMod (p ^ i), ∃ x : A.Ω, ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 8 ∧
    δ = dist ((rep p i g +ᵥ (rep p i h +ᵥ x) : A.Ω) : EuclideanSpace ℝ (Fin n))
      ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))}

/-- *Properties of completed maps*, for a local datum and `0 < ρ < ρ₊`:
1. `ω` is nondecreasing, `ω(t) ≥ t`, `ω(t) → 0` as `t → 0`, and
   `d_∞(Lx, Lx') ≤ ω(d_∞(x, x'))` for `L ∈ 𝓕`;
2. every `L ∈ 𝓕` moves points by at most `2D` in `d_2` and is the identity off `B̄(0, 3/2)`;
3. `â = a·` on `B̄(0, 1)`, and `f_T ∘ â = f_T`;
4. `f_T` is continuous, uniformly continuous into `(Sⁿ, d_S)`, and `f_T = ∞` off `B(0, 17/64)`;
5. `β_i → 0`, and for `|x| ≤ 3/8` each `L_{r_i(g), r_i(h), r_i(g+h), t}(x)` lies within `β_i`
   of `r_i(g+h)·x`. -/
theorem completedMaps_properties (A : LocalDatum p n D ρplus) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ < ρplus) :
    -- (1)
    (Monotone (trackModulus A) ∧ (∀ t, t ≤ trackModulus A t) ∧
      Tendsto (trackModulus A) (𝓝 0) (𝓝 0) ∧
      ∀ L ∈ trackFamily A, ∀ x x' : Torus n, dist (L x) (L x') ≤ trackModulus A (dist x x')) ∧
    -- (2)
    (∀ L ∈ trackFamily A, ∀ x : Torus n,
      Torus.dist₂ (L x) x ≤ 2 * D ∧ (3 / 2 < ‖Torus.lift x‖ → L x = x)) ∧
    -- (3)
    (∀ (a : ℤ_[p]) (x : A.Ω), ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 →
      completedMapEuclid A a x = ((a +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n))) ∧
    (∀ a : ℤ_[p], torusTestMap A ρ ∘ completedMap A a = torusTestMap A ρ) ∧
    -- (4)
    (Continuous (torusTestMap A ρ) ∧
      UniformContinuous (fun x => (torusTestMap A ρ x : Corner.RoundSphere n)) ∧
      ∀ x : Torus n, 17 / 64 ≤ ‖Torus.lift x‖ → torusTestMap A ρ x = ∞) ∧
    -- (5)
    (Tendsto (trackDefect A) atTop (𝓝 0) ∧
      ∀ (i : ℕ) (g h : ZMod (p ^ i)) (t : unitInterval) (x : A.Ω),
        ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 8 →
        dist (trackMapEuclid A (rep p i g) (rep p i h) (rep p i (g + h)) t x)
          ((rep p i (g + h) +ᵥ x : A.Ω) : EuclideanSpace ℝ (Fin n)) ≤ trackDefect A i) := by
  sorry

end HSP.ChainModels

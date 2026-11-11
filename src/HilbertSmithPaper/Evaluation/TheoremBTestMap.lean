import Mathlib
import HilbertSmithPaper.Evaluation.TheoremB
import HilbertSmithPaper.Evaluation.TestMapToPinch
import HilbertSmithPaper.ChainModels.Approximations.TorusTestMap
import HilbertSmithPaper.LocalData.Control.FixedLocalData

/-!
# Theorem B for the test map

Take fixed local data with `n ≥ 1` and buffer radius `R`, and any `s` with `0 < s < R/√n`. Let
`f_T` be the torus test map, `𝔪_{f_T}` its labelled-model class for `n` and `R`, and `Δ_𝟏` the
scalar iterated cut for `n`, `R` and `s`. Then there is `ε ∈ {±1}` with
`σ_tail(Δ_𝟏 𝔪_{f_T}) = [(ε, ε, …)]`.

## Encoding

`theoremB_testMap F hn hs hs'` (the declaration of the article). `f_T` enters as any bundled
continuous map `c` with `⇑c = torusTestMap F.toLocalDatum F.ρ` (it is continuous by the properties
of completed maps, item 4). The radius `R` is the buffer radius `F.R`, positive since
`0 < r < R`. The bound `D ≤ 1/64` of the source is not needed and is omitted.
-/

open HSP.ChainModels

namespace HSP.Evaluation

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {D ρplus : ℝ}

/-- **Theorem B for the test map.** `σ_tail(Δ_𝟏 𝔪_{f_T}) = [(ε, ε, …)]` for some `ε = ±1`. -/
theorem theoremB_testMap (F : FixedLocalData p n D ρplus) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s)
    (hs' : s < F.R / √n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : C(Torus n, Corner.RoundSphere n),
      ⇑c = torusTestMap F.toLocalDatum F.ρ →
      tailSign (GroupSeq.trivial p)
        (Corner.scalarIteratedCut p n F.R s hn (F.r_pos.trans F.r_lt_R) hs hs'
          (germ F.toLocalDatum F.R c)) =
        ((fun _ : ℕ => ε) : Filter.Germ Filter.cofinite ℤ) := by
  obtain ⟨ε, hε, hB⟩ := theoremB n hn
  refine ⟨ε, hε, fun c hc => ?_⟩
  obtain ⟨H, hH, h0, h1⟩ := torusTestMap_homotopic_pinch F hs
  have h0' : ∀ x, H (0, x) = c x := fun x => (h0 x).trans (congrFun hc x).symm
  exact hB p (F.r_pos.trans F.r_lt_R) hs hs' F.toLocalDatum c ⟨⟨⟨H, hH⟩, h0', h1⟩⟩

end HSP.Evaluation

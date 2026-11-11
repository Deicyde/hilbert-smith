import Mathlib
import HilbertSmithPaper.LocalData.Control.FixedLocalDataExists
import HilbertSmithPaper.Compression.TheoremC
import HilbertSmithPaper.Compression.CompressedStandingData
import HilbertSmithPaper.Corner.Theorem.TheoremA
import HilbertSmithPaper.Evaluation.TestMapToPinch
import HilbertSmithPaper.Evaluation.TheoremBTestMap
import HilbertSmithPaper.Proofs.EmptyControlClass
import HilbertSmithPaper.Proofs.IntegerTails

/-!
# Local exclusion

No faithful jointly continuous action of `ℤ_[p]` on a nonempty connected open set
`O ⊆ ℝⁿ` (`IsOpen O`, `IsConnected O`). The action is an `AddAction` on the subtype `O`, the
same form as the conclusion of `HSP.oneChart`.

## Proof

For `n = 0`, `O` is a point. Otherwise take fixed local data on `O` with `D = 1/64` and
`s = R/(2√n)`; the torus test map is continuous (the homotopy to the cubical pinch), Theorem B gives
`σ_tail(Δ_𝟏 𝔪_{f_T}) = [(ε, ε, …)]` with `ε = ±1`, and Theorem C gives the compressed complex with
`U'_* cls = 𝔪_{f_T}`. If the control space is empty the class vanishes, so `ε = 0`
eventually; otherwise Theorem A makes `ε` eventually divisible by `p`, against integer tails.
-/

open Filter

namespace HSP

open Compression ChainModels Evaluation

/-- **Local exclusion.** For a prime `p` and a nonempty connected open set `O ⊆ ℝⁿ`, no jointly
continuous action of `ℤ_[p]` on `O` is faithful. -/
theorem localExclusion (p : ℕ) [Fact p.Prime] (n : ℕ) (O : Set (EuclideanSpace ℝ (Fin n)))
    (hO : IsOpen O) (hc : IsConnected O) [AddAction ℤ_[p] O] [ContinuousVAdd ℤ_[p] O] :
    ¬ FaithfulVAdd ℤ_[p] O := by
  intro hfaith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h01 : (0 : ℤ_[p]) = 1 :=
      hfaith.eq_of_vadd_eq_vadd fun x => Subsingleton.elim _ _
    exact zero_ne_one h01
  · let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨O, hO⟩
    have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hc
    let _ : AddAction ℤ_[p] U := ‹AddAction ℤ_[p] O›
    have : ContinuousVAdd ℤ_[p] U := ‹ContinuousVAdd ℤ_[p] O›
    have : FaithfulVAdd ℤ_[p] U := hfaith
    obtain ⟨ρplus, -, -, ⟨F⟩⟩ :=
      exists_fixedLocalData (p := p) (n := n) (M := U) (D := 1 / 64) (by norm_num) le_rfl
    have hR : 0 < F.R := F.r_pos.trans F.r_lt_R
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    set s := F.R / (2 * √(n : ℝ)) with hsdef
    have hs : 0 < s := by positivity
    have hs' : s < F.R / √n := by
      rw [hsdef]
      exact div_lt_div_of_pos_left hR hsq (by linarith)
    -- the test map as a continuous map
    obtain ⟨H, hHc, hH0, -⟩ := torusTestMap_homotopic_pinch F hs
    let c : C(Torus n, Corner.RoundSphere n) :=
      ⟨fun x => H (0, x), hHc.comp (continuous_const.prodMk continuous_id)⟩
    have hcT : ⇑c = torusTestMap F.toLocalDatum F.ρ := funext hH0
    -- Theorem B for the test map
    obtain ⟨ε, hε, hσB⟩ := theoremB_testMap F hn hs hs'
    have hσ := hσB c hcT
    -- Theorem C
    obtain ⟨P, hX, d, hd, φ, hφ, -, -, hconc, hact, himg⟩ := theoremC F
    have himg' := himg c hH0
    rcases isEmpty_or_nonempty F.T with hT | hT
    · -- empty control space: the class vanishes
      rw [cls_eq_zero_of_isEmpty, map_zero] at himg'
      rw [← himg', map_zero, map_zero] at hσ
      have hev : ∀ᶠ i in (cofinite : Filter ℕ), ε = 0 :=
        Germ.coe_eq.1 (hσ.symm.trans Germ.coe_zero.symm)
      obtain ⟨i, hi⟩ := hev.exists
      rcases hε with h | h <;> omega
    · -- nonempty control space: Theorem A
      obtain ⟨Γ, -⟩ := hact hs hs'
      have hdvd := Corner.theoremA (standingData F hs hs') P hconc d hd φ hφ Γ
        (fun _ => ε) (by rw [← himg'] at hσ; exact hσ.symm)
      exact not_eventually_unit_and_dvd (Fact.out : p.Prime).one_lt (fun _ => ε)
        ⟨Eventually.of_forall fun _ => hε, hdvd⟩

end HSP

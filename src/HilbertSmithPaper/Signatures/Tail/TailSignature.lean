import HilbertSmithPaper.Signatures.Tail.TailLift
import HilbertSmithPaper.Signatures.Tail.TailLiftEventual
import HilbertSmithPaper.Signatures.LFour.IntegerSignature
import HilbertSmithPaper.LTheory.Comparison.FreeComparison

/-!
# The tail signature

Let `𝐆` be a group sequence. `σ_tail : 𝕃_4(𝒱_𝐆) → ℤ^ℕ ⧸ ℤ^(ℕ)` sends `x` to the class of
`(σ_{G_i}(cls⁻¹ (π_i)_* y))_i`, for a chosen `y ∈ 𝕃_4(𝒫_𝐆)` with `q_* y = x`. The definition is
an additive homomorphism; its two proof obligations, that the class does not depend on the lift
`y` and that the map is additive, are discharged in the construction.

Lean: `ℤ^ℕ ⧸ ℤ^(ℕ)` is the group `Filter.Germ (Filter.cofinite : Filter ℕ) ℤ` of germs at the
cofinite filter.

This rests on the open statements Lemma U, through the point comparison and the coordinate lemmas,
and lifting, through the localization boundary of the point filtration.
-/

namespace HSP

variable {p : ℕ} (G : GroupSeq p)

/-- `y ↦ [(σ_{G_i}(cls⁻¹ (π_i)_* y))_i]` on `𝕃_4(𝒫_𝐆)`. -/
private noncomputable def liftSign :
    ultL (PCat G) 4 →+ Filter.Germ (Filter.cofinite : Filter ℕ) ℤ :=
  (Filter.Germ.coeAddHom Filter.cofinite).comp <| AddMonoidHom.pi fun i =>
    (intSign.comp (AddEquiv.ofBijective _ (cls_bijective_free G i 4)).symm.toAddMonoidHom).comp
      (ultL.map (PCat.proj G i) 4)

variable {G}

/-- Lifts with the same image under `q_*` have the same signature germ. -/
private theorem liftSign_eq {y y' : ultL (PCat G) 4}
    (h : ultL.map (VCat.q G) 4 y = ultL.map (VCat.q G) 4 y') : liftSign G y = liftSign G y' :=
  Filter.Germ.coe_eq.2 <| (tail_lift_eventually G y y' h).mono fun i hi => by
    simp only [AddMonoidHom.pi_apply, AddMonoidHom.comp_apply, hi]

variable (G)

/-- **The tail signature** `σ_tail : 𝕃_4(𝒱_𝐆) → ℤ^ℕ ⧸ ℤ^(ℕ)`,
`x ↦ [(σ_{G_i}(cls⁻¹ (π_i)_* y))_i]` for a chosen lift `y` of `x`. -/
noncomputable def tailSign : ultL (VCat G) 4 →+ Filter.Germ (Filter.cofinite : Filter ℕ) ℤ where
  toFun x := liftSign G (tail_lift G x).choose
  map_zero' := by
    rw [← map_zero (liftSign G)]
    exact liftSign_eq ((tail_lift G 0).choose_spec.trans (map_zero _).symm)
  map_add' x x' := by
    rw [← map_add]
    exact liftSign_eq ((tail_lift G (x + x')).choose_spec.trans (by
      rw [map_add, (tail_lift G x).choose_spec, (tail_lift G x').choose_spec]))

end HSP

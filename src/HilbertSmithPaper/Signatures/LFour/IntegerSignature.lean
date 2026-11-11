import Mathlib
import HilbertSmithPaper.Signatures.Forms.SignatureSplitting
import HilbertSmithPaper.Signatures.LFour.SignatureHom
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingExists
import HilbertSmithPaper.Signatures.Forms.FormSignatureIdentity

/-!
# Integer signature

`σ_G : L^p_4(Free(ℚ[G])) → ℤ`, `[C, φ] ↦ dim V⁺ - dim V⁻` for an invariant signature splitting
`V⁺ ⊕ V⁻` of the middle form `b_C` (`HSP.intSign`), is well defined and additive.

Lean encoding: on a representative the splitting is chosen from the existence of invariant
signature splittings (the middle form being nonsingular, symmetric and invariant). By the
identity value, `dim V⁺ - dim V⁻ = sign_{b_C}(1) = Sign_G(C, φ)(0)` (`0` the identity of the
additively written `G`), which depends only on the class and is additive in it because the
equivariant signature on `L^p_4` is an additive homomorphism; `ℤ → ℝ` is injective.
-/

open CategoryTheory CategoryTheory.Idempotents Module

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- An invariant signature splitting of the middle form. -/
private theorem exists_splitting (x : SymPoincare (Karoubi (FreeCat G)) 4) :
    ∃ Vp Vn : Submodule ℝ (realHco x.C 2),
      IsSignatureSplitting (middleForm x) realHco.rep Vp Vn :=
  exists_signatureSplitting _ _ (middleForm_nonsingular x).1 (middleForm_nonsingular x).2.1
    (middleForm_nonsingular x).2.2

/-- `dim V⁺ - dim V⁻` for the chosen invariant signature splitting of `b_C`. -/
private noncomputable def intSignRep (x : SymPoincare (Karoubi (FreeCat G)) 4) : ℤ :=
  (finrank ℝ (exists_splitting x).choose : ℤ) - finrank ℝ (exists_splitting x).choose_spec.choose

private theorem intSignRep_cast (x : SymPoincare (Karoubi (FreeCat G)) 4) :
    (intSignRep x : ℝ) = complexSign x 0 := by
  have hs := (exists_splitting x).choose_spec.choose_spec
  obtain ⟨hb, hnd, hρ⟩ := middleForm_nonsingular x
  rw [complexSign, ofAdd_zero, formSign_one hb hnd hρ hs.isCompl hs.pos hs.neg, intSignRep]

/-- **The integer signature** `σ_G : L^p_4(Free(ℚ[G])) → ℤ`, `[C, φ] ↦ dim V⁺ - dim V⁻`. -/
noncomputable def intSign : Lp (FreeCat G) 4 →+ ℤ :=
  AddMonoidHom.mk' (Quotient.lift intSignRep fun x y hxy => Int.cast_injective (α := ℝ) (by
      rw [intSignRep_cast, intSignRep_cast, ← sign_mk, ← sign_mk]
      exact congrArg (fun a => sign a 0) (Quotient.sound hxy)))
    fun a b => by
      induction a using Quotient.inductionOn with | h x => ?_
      induction b using Quotient.inductionOn with | h y => ?_
      refine Int.cast_injective (α := ℝ) ?_
      change (intSignRep (SymPoincare.sum x y) : ℝ) = ((intSignRep x + intSignRep y : ℤ) : ℝ)
      rw [Int.cast_add, intSignRep_cast, intSignRep_cast, intSignRep_cast, ← sign_mk, ← sign_mk,
        ← sign_mk, ← Pi.add_apply, ← map_add]
      rfl

end HSP

import Mathlib
import HilbertSmithPaper.Signatures.LFour.BoundarySignatureZero
import HilbertSmithPaper.Signatures.LFour.MiddleFormSum
import HilbertSmithPaper.Signatures.LFour.MiddleFormNeg
import HilbertSmithPaper.Signatures.Forms.FormSignatureIsometry
import HilbertSmithPaper.Signatures.Forms.FormSignatureSum
import HilbertSmithPaper.Signatures.Forms.FormSignatureNeg
import HilbertSmithPaper.LTheory.Base.Groups.LGroupAdd

/-!
# The equivariant signature on `L^p_4`

`Sign_G : L^p_4(Free(ℚ[G])) → (G → ℝ)`, `[C, φ] ↦ Sign_G(C, φ)`, is a well-defined additive
homomorphism (`HSP.sign`, `HSP.sign_mk`).

Proof. If `(C'', φ'')` is the sum of `(C, φ)` and `(C', φ')`, the middle form of a sum and
isometry invariance give `Sign_G(C'') = sign_{b_C ⊥ b_{C'}}`, and additivity of the signature of
forms gives `Sign_G(C) + Sign_G(C')`. If `(C, φ)` and `(C', φ')` are cobordant, then
`(C ⊕ C', φ ⊕ (-φ'))` is a boundary, of signature zero; by the above and the middle form of the
negative with negation of the signature of forms, this signature is
`Sign_G(C) - Sign_G(C')`. The sum in `L^p_4` is `⊕`, so the map is additive.
-/

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits

namespace HSP

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The signature of a sum is the sum of the signatures. -/
private theorem complexSign_sum (x y z : SymPoincare (Karoubi (FreeCat G)) 4)
    (h : (⟨z.C, z.φ⟩ : Σ C : ChainComplex (Karoubi (FreeCat G)) ℤ, (StructureCx C).X 4) =
      ⟨x.C ⊞ y.C, StructureCx.sum x.φ y.φ⟩) :
    complexSign z = complexSign x + complexSign y := by
  obtain ⟨hbij, hiso, hequiv⟩ := middleForm_sum x y z h
  obtain ⟨hsx, hnx, hix⟩ := middleForm_nonsingular x
  obtain ⟨hsy, hny, hiy⟩ := middleForm_nonsingular y
  funext g
  rw [complexSign, formSign_congr (LinearEquiv.ofBijective _ hbij) (fun u v => ?_)
    (fun a u => ?_), formSign_sum hsx hnx hix hsy hny hiy]
  · rfl
  · simp only [LinearEquiv.ofBijective_apply, LinearMap.add_apply, LinearMap.compl₁₂_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    exact (hiso u v).symm
  · simp only [LinearEquiv.ofBijective_apply, Representation.prod_apply_apply]
    exact hequiv a u

/-- The signature of the negative is the negative of the signature. -/
private theorem complexSign_neg (y : SymPoincare (Karoubi (FreeCat G)) 4) :
    complexSign (SymPoincare.neg y) = -complexSign y := by
  funext g
  change formSign (middleForm (SymPoincare.neg y)) realHco.rep _ = -formSign (middleForm y) _ _
  rw [middleForm_neg]
  exact formSign_neg _ _ _

/-- Cobordant complexes have the same signature. -/
private theorem complexSign_eq_of_cobordant (x y : SymPoincare (Karoubi (FreeCat G)) 4)
    (hxy : Cobordant x y) : complexSign x = complexSign y := by
  obtain ⟨W, hW⟩ := hxy
  have h0 := complexSign_boundary W
  rw [complexSign_sum x (SymPoincare.neg y) W.boundary hW, complexSign_neg] at h0
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact h0)

/-- **The equivariant signature on `L^p_4`**, `[C, φ] ↦ Sign_G(C, φ)`, an additive homomorphism. -/
noncomputable def sign : Lp (FreeCat G) 4 →+ (G → ℝ) :=
  AddMonoidHom.mk' (Quotient.lift complexSign complexSign_eq_of_cobordant) fun a b => by
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    exact complexSign_sum x y (SymPoincare.sum x y) (SymPoincare.sum_spec x y)

theorem sign_mk (x : SymPoincare (Karoubi (FreeCat G)) 4) :
    sign (LGroup.mk x) = complexSign x := rfl

end HSP

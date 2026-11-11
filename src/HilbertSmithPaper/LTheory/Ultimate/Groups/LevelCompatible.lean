import HilbertSmithPaper.LTheory.Ultimate.Groups.UltimateStageMap

/-!
# Stages are compatible with the transition

`ι_{j+1} ∘ t = ι_j` on `L^{⟨-j⟩}_k(A)`. Hence `ι_{j+m} ∘ t^m = ι_j` for every `m ≥ 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The iterated transition `t^m : L^{⟨-j⟩}_k(A) → L^{⟨-j-m⟩}_k(A)`. -/
noncomputable def transitionIter (k : ℤ) (j : ℕ) : ∀ m : ℕ, lowerL A j k →+ lowerL A (j + m) k
  | 0 => AddMonoidHom.id _
  | m + 1 => (transitionLower A (j + m) k).comp (transitionIter k j m)

/-- `ι_{j+1} ∘ t = ι_j`, and hence `ι_{j+m} ∘ t^m = ι_j`. -/
theorem ultL.of_trans (k : ℤ) :
    (∀ j : ℕ, (ultL.of A k (j + 1)).comp (transitionLower A j k) = ultL.of A k j) ∧
    ∀ j m : ℕ, (ultL.of A k (j + m)).comp (transitionIter A k j m) = ultL.of A k j := by
  have h1 : ∀ j : ℕ, (ultL.of A k (j + 1)).comp (transitionLower A j k) = ultL.of A k j := by
    intro j
    have h := colimit.w (lowerLSeq A k) (homOfLE (Nat.le_add_right j 1))
    rw [lowerLSeq, Functor.ofSequence_map_homOfLE_succ] at h
    ext x
    exact congrArg (fun f => AddCommGrpCat.Hom.hom f x) h
  refine ⟨h1, fun j m => ?_⟩
  induction m with
  | zero => rfl
  | succ m ih =>
    change (ultL.of A k (j + m + 1)).comp
      ((transitionLower A (j + m) k).comp (transitionIter A k j m)) = _
    rw [← AddMonoidHom.comp_assoc, h1, ih]

end HSP

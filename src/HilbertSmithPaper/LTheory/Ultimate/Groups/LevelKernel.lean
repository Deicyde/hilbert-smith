import HilbertSmithPaper.LTheory.Ultimate.Groups.LevelCompatible

/-!
# Kernels of the stage maps

For `x ∈ L^{⟨-j⟩}_k(A)`, `ι_j x = 0` if and only if `t^m x = 0` in `L^{⟨-j-m⟩}_k(A)` for some
`m ≥ 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- The map of the sequence from stage `j` to stage `j + m` is `t^m`. -/
private lemma lowerLSeq_map (k : ℤ) (j m : ℕ) :
    (lowerLSeq A k).map (homOfLE (Nat.le_add_right j m)) =
      AddCommGrpCat.ofHom (transitionIter A k j m) := by
  induction m with
  | zero => exact (lowerLSeq A k).map_id j
  | succ m ih =>
    have h : homOfLE (Nat.le_add_right j (m + 1)) =
        homOfLE (Nat.le_add_right j m) ≫ homOfLE (Nat.le_add_right (j + m) 1) := rfl
    rw [h, Functor.map_comp, ih]
    change _ ≫ (Functor.ofSequence (C := AddCommGrpCat.{max u v})
      fun i => AddCommGrpCat.ofHom (transitionLower A i k)).map _ = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    rfl

/-- `ι_j x = 0` if and only if `t^m x = 0` for some `m`. -/
theorem ultL.of_eq_zero_iff (k : ℤ) (j : ℕ) (x : lowerL A j k) :
    ultL.of A k j x = 0 ↔ ∃ m : ℕ, transitionIter A k j m x = 0 := by
  constructor
  · intro hx
    have : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{max u v}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    have h0 : ultL.of A k j x = ultL.of A k j 0 := by rw [hx, map_zero]
    obtain ⟨n, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq (lowerLSeq A k) x 0 h0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
    refine ⟨m, ?_⟩
    have e : f = homOfLE (Nat.le_add_right j m) := Subsingleton.elim _ _
    subst e
    have hg : ((lowerLSeq A k).map g) 0 = 0 := map_zero _
    rw [hg, lowerLSeq_map] at hfg
    exact hfg
  · rintro ⟨m, hm⟩
    rw [← (ultL.of_trans A k).2 j m, AddMonoidHom.comp_apply, hm, map_zero]

end HSP

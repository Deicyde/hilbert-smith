import HilbertSmithPaper.LTheory.Base.Categories.FiltrationIdeal

/-!
# Maps factoring through a dual-closed subcategory form an ideal

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality, the maps factoring through an
object of `𝒰` form a ℚ-linear ideal closed under `*`: if `f` factors through `V` and `g`
through `W`, then `f + g` factors through a sum of `V` and `W` in `𝒰`, and `f = a ≫ b` gives
`f^* = b^* ≫ a^*` through `V^*`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

namespace FiltQuot

variable {U : ObjectProperty A}

private lemma ideal_zero [IsDualAdditive U] {M N : A} : ideal U (0 : M ⟶ N) := by
  obtain ⟨Z, hZ, -⟩ := IsDualAdditive.exists_zero (U := U)
  exact ⟨Z, hZ, 0, 0, by simp⟩

private lemma ideal_add [IsDualAdditive U] {M N : A} {f g : M ⟶ N} (hf : ideal U f) (hg : ideal U g) :
    ideal U (f + g) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  obtain ⟨W, hW, c, d, rfl⟩ := hg
  obtain ⟨P, -, hP⟩ := IsDualAdditive.exists_biprod hV hW
  refine ⟨P.pt, hP, a ≫ P.inl + c ≫ P.inr, P.fst ≫ b + P.snd ≫ d, ?_⟩
  simp

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
private lemma ideal_neg {M N : A} {f : M ⟶ N} (hf : ideal U f) : ideal U (-f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, -a, b, by simp⟩

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma ideal_smul {M N : A} (c : ℚ) {f : M ⟶ N} (hf : ideal U f) : ideal U (c • f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, c • a, b, by simp⟩

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
private lemma ideal_comp_left {L M N : A} (h : L ⟶ M) {f : M ⟶ N} (hf : ideal U f) :
    ideal U (h ≫ f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, h ≫ a, b, by simp⟩

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
private lemma ideal_comp_right {M N P : A} {f : M ⟶ N} (hf : ideal U f) (h : N ⟶ P) :
    ideal U (f ≫ h) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨V, hV, a, b ≫ h, by simp⟩

private lemma ideal_dual [IsDualAdditive U] {M N : A} {f : M ⟶ N} (hf : ideal U f) :
    ideal U (dualHom f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := hf
  exact ⟨dual V, IsDualAdditive.dual_mem hV, dualHom b, dualHom a, by simp⟩

/-- **Maps factoring through a dual-closed subcategory form an ideal.** `I_𝒰` contains `0` and is
closed under sums, negatives, rational multiples, composition on either side and the duality. -/
theorem ideal_closed (U : ObjectProperty A) [IsDualAdditive U] :
    (∀ {M N : A}, ideal U (0 : M ⟶ N)) ∧
    (∀ {M N : A} {f g : M ⟶ N}, ideal U f → ideal U g → ideal U (f + g)) ∧
    (∀ {M N : A} {f : M ⟶ N}, ideal U f → ideal U (-f)) ∧
    (∀ {M N : A} (c : ℚ) {f : M ⟶ N}, ideal U f → ideal U (c • f)) ∧
    (∀ {L M N : A} (h : L ⟶ M) {f : M ⟶ N}, ideal U f → ideal U (h ≫ f)) ∧
    (∀ {M N P : A} {f : M ⟶ N}, ideal U f → ∀ h : N ⟶ P, ideal U (f ≫ h)) ∧
    (∀ {M N : A} {f : M ⟶ N}, ideal U f → ideal U (dualHom f)) :=
  ⟨ideal_zero, ideal_add, ideal_neg, ideal_smul, ideal_comp_left, ideal_comp_right, ideal_dual⟩

end FiltQuot

end HSP

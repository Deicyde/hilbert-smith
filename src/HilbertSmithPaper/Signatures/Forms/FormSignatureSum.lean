import Mathlib
import HilbertSmithPaper.Signatures.Forms.SignatureSplitting
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingExists
import HilbertSmithPaper.Signatures.LFour.SignatureSplittingIndependence

/-!
# Additivity

`sign_{b ⊥ b'} = sign_b + sign_{b'}` on `W × W'` with the diagonal action. The orthogonal sum
`b ⊥ b'` is `((x, x'), (y, y')) ↦ b x y + b' x' y'`. The products of two signature splittings
form a signature splitting of the sum, and the trace of a product map is the sum of the traces.
-/

namespace HSP

open Module

variable {G W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']

/-- The orthogonal sum of two splittings is a splitting of the orthogonal sum. -/
private lemma IsSignatureSplitting.prod [Monoid G] {b : LinearMap.BilinForm ℝ W}
    {b' : LinearMap.BilinForm ℝ W'} {ρ : Representation ℝ G W} {ρ' : Representation ℝ G W'}
    {Vp Vn : Submodule ℝ W} {Vp' Vn' : Submodule ℝ W'} (h : IsSignatureSplitting b ρ Vp Vn)
    (h' : IsSignatureSplitting b' ρ' Vp' Vn') :
    IsSignatureSplitting (b.compl₁₂ (.fst ℝ W W') (.fst ℝ W W') +
      b'.compl₁₂ (.snd ℝ W W') (.snd ℝ W W')) (ρ.prod ρ') (Vp.prod Vp') (Vn.prod Vn') where
  mapsTo_pos g x hx := ⟨h.mapsTo_pos g _ hx.1, h'.mapsTo_pos g _ hx.2⟩
  mapsTo_neg g x hx := ⟨h.mapsTo_neg g _ hx.1, h'.mapsTo_neg g _ hx.2⟩
  isCompl := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff, Submodule.prod_inf_prod,
      Submodule.prod_sup_prod, h.isCompl.inf_eq_bot, h'.isCompl.inf_eq_bot,
      h.isCompl.sup_eq_top, h'.isCompl.sup_eq_top, Submodule.prod_bot, Submodule.prod_top]
    exact ⟨rfl, rfl⟩
  pos x hx h0 := by
    obtain ⟨x, x'⟩ := x
    have h1 : ∀ y ∈ Vp, 0 ≤ b y y := fun y hy => by
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      · exact (h.pos y hy hy0).le
    have h2 : ∀ y ∈ Vp', 0 ≤ b' y y := fun y hy => by
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      · exact (h'.pos y hy hy0).le
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
    rcases eq_or_ne x 0 with rfl | hx0
    · have hx' : x' ≠ 0 := by rintro rfl; exact h0 rfl
      linarith [h'.pos x' hx.2 hx', h1 0 hx.1]
    · linarith [h.pos x hx.1 hx0, h2 x' hx.2]
  neg x hx h0 := by
    obtain ⟨x, x'⟩ := x
    have h1 : ∀ y ∈ Vn, b y y ≤ 0 := fun y hy => by
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      · exact (h.neg y hy hy0).le
    have h2 : ∀ y ∈ Vn', b' y y ≤ 0 := fun y hy => by
      rcases eq_or_ne y 0 with rfl | hy0
      · simp
      · exact (h'.neg y hy hy0).le
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
    rcases eq_or_ne x 0 with rfl | hx0
    · have hx' : x' ≠ 0 := by rintro rfl; exact h0 rfl
      linarith [h'.neg x' hx.2 hx', h1 0 hx.1]
    · linarith [h.neg x hx.1 hx0, h2 x' hx.2]

/-- The trace of a product map on a product of invariant subspaces. -/
private lemma trace_restrict_prodMap [FiniteDimensional ℝ W] [FiniteDimensional ℝ W']
    {F : W × W' →ₗ[ℝ] W × W'} {f : W →ₗ[ℝ] W} {f' : W' →ₗ[ℝ] W'} (hF : F = f.prodMap f')
    {V : Submodule ℝ W} {V' : Submodule ℝ W'} (hV : ∀ x ∈ V, f x ∈ V)
    (hV' : ∀ x ∈ V', f' x ∈ V') (hVV : ∀ x ∈ V.prod V', F x ∈ V.prod V') :
    LinearMap.trace ℝ _ (F.restrict hVV) =
      LinearMap.trace ℝ V (f.restrict hV) + LinearMap.trace ℝ V' (f'.restrict hV') := by
  subst hF
  rw [← LinearMap.trace_prodMap', ← LinearMap.trace_conj' _ (Submodule.prodEquiv V V')]
  congr 1

/-- **Additivity.** `sign_{b ⊥ b'} = sign_b + sign_{b'}` on `W × W'` with the diagonal action. -/
theorem formSign_sum [Group G] [Finite G] [FiniteDimensional ℝ W] [FiniteDimensional ℝ W']
    {b : LinearMap.BilinForm ℝ W} {b' : LinearMap.BilinForm ℝ W'} {ρ : Representation ℝ G W}
    {ρ' : Representation ℝ G W'} (hb : b.IsSymm) (hnd : b.Nondegenerate)
    (hρ : ∀ g x y, b (ρ g x) (ρ g y) = b x y) (hb' : b'.IsSymm) (hnd' : b'.Nondegenerate)
    (hρ' : ∀ g x y, b' (ρ' g x) (ρ' g y) = b' x y) (g : G) :
    formSign (b.compl₁₂ (.fst ℝ W W') (.fst ℝ W W') + b'.compl₁₂ (.snd ℝ W W') (.snd ℝ W W'))
      (ρ.prod ρ') g = formSign b ρ g + formSign b' ρ' g := by
  obtain ⟨Vp, Vn, h⟩ := exists_signatureSplitting b ρ hb hnd hρ
  obtain ⟨Vp', Vn', h'⟩ := exists_signatureSplitting b' ρ' hb' hnd' hρ'
  rw [formSign_eq_of_splitting (h.prod h') g, formSign_eq_of_splitting h g,
    formSign_eq_of_splitting h' g]
  rw [trace_restrict_prodMap (F := (ρ.prod ρ') g) rfl (h.mapsTo_pos g) (h'.mapsTo_pos g),
    trace_restrict_prodMap (F := (ρ.prod ρ') g) rfl (h.mapsTo_neg g) (h'.mapsTo_neg g)]
  ring

end HSP

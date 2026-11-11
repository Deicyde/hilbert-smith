import HilbertSmithPaper.Categories.Supports.SupportSubcategory
import HilbertSmithPaper.Categories.Asymptotic.RestrictionSubBasis
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient

/-!
# Support ideal

Let the `C_p`-action on `X` be isometric and `S ⊆ X` invariant. A morphism `[u] : M → N` of
`𝒜_𝐆(X)` factors through an object of `𝒜_S` (`FiltQuot.ideal (supp S)`) if and only if for every
`ε > 0`, eventually both endpoint labels of every nonzero entry of `u_i` lie in the open
`ε`-thickening of `S` (`HSP.factorsThrough_supp_iff`).

The (⇐) direction restricts the source to the indices of its nonzero columns
(`HSP.AsymPre.restrict`). The companions `HSP.vadd_mem_thickening(_iff)` record that for an
invariant `S` and an isometric action, `c +ᵥ y` lies in the `ε`-thickening of `S` iff `y` does.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology Metric
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

namespace AsymPre

/-- An entry bound for the propagation: a nonzero entry joins labels at distance `≤ prop`. -/
private theorem nndist_le_prop {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X) (l' : B' → X)
    (u : Matrix B' B ℚ) {b' : B'} {b : B} (h : u b' b ≠ 0) : nndist (l' b') (l b) ≤ prop l l' u :=
  Finset.le_sup (s := Finset.univ.filter fun q : B' × B => u q.1 q.2 ≠ 0) (b := (b', b))
    (f := fun q : B' × B => nndist (l' q.1) (l q.2))
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

end AsymPre

variable [IsIsometricVAdd (ZMod p) X] {S : Set X}

/-- For an invariant `S` and an isometric action, `c +ᵥ y` is in the `ε`-thickening of `S` as soon
as `y` is. -/
theorem vadd_mem_thickening (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) (c : ZMod p) {ε : ℝ} {y : X}
    (hy : y ∈ thickening ε S) : c +ᵥ y ∈ thickening ε S := by
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hy
  exact mem_thickening_iff.2 ⟨c +ᵥ z, hS c z hz, by rwa [dist_vadd]⟩

theorem vadd_mem_thickening_iff (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) (c : ZMod p) {ε : ℝ}
    {y : X} : c +ᵥ y ∈ thickening ε S ↔ y ∈ thickening ε S :=
  ⟨fun h => by simpa using vadd_mem_thickening hS (-c) h, vadd_mem_thickening hS c⟩

/-- **Support ideal.** For an invariant `S` (and an isometric action), `[u] : M → N` factors
through an object of `𝒜_S` if and only if for every `ε > 0`, eventually both endpoint labels of
every nonzero entry of `u_i` lie in the `ε`-thickening of `S`. -/
theorem factorsThrough_supp_iff (hS : ∀ c : ZMod p, ∀ x ∈ S, c +ᵥ x ∈ S) {M N : AsymPre G X}
    (u : M ⟶ N) :
    FiltQuot.ideal (supp S) (AsymCat.mkHom u) ↔
      ∀ ε > 0, ∀ᶠ i in atTop, ∀ a b, FreeCat.mat (AsymPre.coord u i) a b ≠ 0 →
        N.label i a ∈ thickening ε S ∧ M.label i b ∈ thickening ε S := by
  constructor
  · rintro ⟨V, hV, f, g, hfg⟩
    obtain ⟨f, rfl⟩ := AsymCat.mkHom_surjective f
    obtain ⟨g, rfl⟩ := AsymCat.mkHom_surjective g
    rw [← Functor.map_comp, AsymCat.mkHom_eq_iff] at hfg
    intro ε hε
    have h2 : (0 : ℝ) < ε / 2 := half_pos hε
    have hf := (NNReal.tendsto_coe.2 (AsymPre.tendsto_prop f)).eventually (gt_mem_nhds h2)
    have hg := (NNReal.tendsto_coe.2 (AsymPre.tendsto_prop g)).eventually (gt_mem_nhds h2)
    filter_upwards [hfg, hV _ h2, hf, hg] with i hi hVi hfi hgi a b hab
    rw [hi, AsymPre.coord_comp, FreeCat.mat_comp, Matrix.mul_apply] at hab
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    have hgw := NNReal.coe_le_coe.2
      (AsymPre.nndist_le_prop (V.as.label i) (N.label i) _ (left_ne_zero_of_mul hw))
    have hfw := NNReal.coe_le_coe.2
      (AsymPre.nndist_le_prop (M.label i) (V.as.label i) _ (right_ne_zero_of_mul hw))
    have hw' : V.as.label i w ∈ thickening (ε / 2) S := vadd_mem_thickening hS _ (hVi w.2)
    obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hw'
    rw [coe_nndist] at hgw hfw
    refine ⟨mem_thickening_iff.2 ⟨z, hz, ?_⟩, mem_thickening_iff.2 ⟨z, hz, ?_⟩⟩
    · have := lt_of_le_of_lt hgw hgi
      linarith [dist_triangle (N.label i a) (V.as.label i w) z]
    · have := lt_of_le_of_lt hfw hfi
      linarith [dist_triangle (M.label i b) (V.as.label i w) z, dist_comm (M.label i b)
        (V.as.label i w)]
  · intro h
    let P : ∀ i, Fin (M.n i) → Prop := fun i k =>
      ∃ (g : G.G i) (a : G.G i × Fin (N.n i)), FreeCat.mat (AsymPre.coord u i) a (g, k) ≠ 0
    refine ⟨⟨M.restrict P⟩, fun ε hε => ?_, AsymCat.mkHom (M.restrictPro P),
      AsymCat.mkHom (M.restrictInc P ≫ u), ?_⟩
    · filter_upwards [h ε hε] with i hi k
      obtain ⟨g, a, hga⟩ := AsymPre.restrictEmb_mem (P := P) k
      exact (vadd_mem_thickening_iff hS _).1 (hi a _ hga).2
    · classical
      rw [← Functor.map_comp, ← Category.assoc, AsymPre.restrictPro_restrictInc,
        AsymPre.trunc_comp_eq]
      exact fun i a b hab => ⟨b.1, a, hab⟩

end HSP

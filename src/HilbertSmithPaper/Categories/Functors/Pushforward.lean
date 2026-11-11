import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Pushforward of labels

For an equivariant continuous map `f : X → X'` of compact metric `C_p`-spaces,
`f_* : 𝒜_𝐆(X) → 𝒜_𝐆(X')` is the strict duality functor `(n_i, x_i) ↦ (n_i, f ∘ x_i)`,
`[u] ↦ [u]`.

Lean encoding. Equivariance gives `λ'_i = f ∘ λ_i` for the labels, and uniform continuity of `f`
(from compactness of `X`) gives `prop(f_* u_i) → 0` when `prop(u_i) → 0`. On sequences
`HSP.AsymPre.push` keeps the matrices; it respects eventual equality, so it descends to the
quotient. `HSP.push f` is the duality functor, with `ξ = id`, strict (`HSP.push_isStrict`).
Neither isometry of the actions nor compactness of `X'` is needed.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p}
  {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]
  {X' : Type*} [MetricSpace X'] [AddAction (ZMod p) X']

/-- Uniformly continuous maps keep propagation tending to `0`. -/
private theorem tendsto_prop_comp {f : X → X'} (hf : UniformContinuous f) {B B' : ℕ → Type}
    [∀ i, Fintype (B i)] [∀ i, Fintype (B' i)] (l : ∀ i, B i → X) (l' : ∀ i, B' i → X)
    (u : ∀ i, Matrix (B' i) (B i) ℚ)
    (h : Tendsto (fun i => prop (l i) (l' i) (u i)) atTop (𝓝 0)) :
    Tendsto (fun i => prop (f ∘ l i) (f ∘ l' i) (u i)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => absurd ha (not_lt.2 zero_le), fun a ha => ?_⟩
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1 hf (a / 2) (by positivity)
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ≥0) < ⟨δ, hδ.le⟩ from hδ))] with i hi
  refine lt_of_le_of_lt (Finset.sup_le fun q hq => ?_) (NNReal.half_lt_self ha.ne')
  have hle : nndist (l' i q.1) (l i q.2) ≤ prop (l i) (l' i) (u i) :=
    Finset.le_sup (f := fun q : B' i × B i => nndist (l' i q.1) (l i q.2)) hq
  have hd : dist (l' i q.1) (l i q.2) < δ := lt_of_le_of_lt hle hi
  have := hfδ hd
  rw [← NNReal.coe_le_coe, coe_nndist, NNReal.coe_div, NNReal.coe_two]
  exact this.le

namespace AsymPre

variable (f : X → X')

/-- The pushed-forward object `(n_i, f ∘ x_i)`. -/
def pushObj (M : AsymPre G X) : AsymPre G X' := ⟨M.n, fun i => f ∘ M.x i⟩

omit [MetricSpace X] [MetricSpace X'] in
theorem label_pushObj (hfe : ∀ (c : ZMod p) (x : X), f (c +ᵥ x) = c +ᵥ f x)
    (M : AsymPre G X) (i : ℕ) : (pushObj f M).label i = f ∘ M.label i :=
  funext fun _ => (hfe _ _).symm

variable {f}

/-- Pushforward on sequences: the matrices are unchanged. -/
@[simps]
def push (hf : Continuous f) (hfe : ∀ (c : ZMod p) (x : X), f (c +ᵥ x) = c +ᵥ f x)
    [CompactSpace X] : AsymPre G X ⥤ AsymPre G X' where
  obj M := pushObj f M
  map {M N} u := homMk (fun i => coord u i) (by
    have h := tendsto_prop_comp (CompactSpace.uniformContinuous_of_continuous hf)
      (fun i => M.label i) (fun i => N.label i) (fun i => FreeCat.mat (coord u i))
      (tendsto_prop u)
    refine (tendsto_congr fun i => ?_).2 h
    show prop ((pushObj f M).label i) ((pushObj f N).label i) _ = _
    rw [label_pushObj f hfe, label_pushObj f hfe]
    rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

end AsymPre

variable {f : X → X'} (hf : Continuous f) (hfe : ∀ (c : ZMod p) (x : X), f (c +ᵥ x) = c +ᵥ f x)
  [CompactSpace X]

/-- The underlying functor of the pushforward `f_* : 𝒜_𝐆(X) ⥤ 𝒜_𝐆(X')`. -/
def pushFunctor : AsymCat G X ⥤ AsymCat G X' :=
  CategoryTheory.Quotient.lift (asymRel G X)
    (AsymPre.push hf hfe ⋙ Quotient.functor (asymRel G X')) fun _ _ _ _ h =>
      CategoryTheory.Quotient.sound _ (h.mono fun _ h => h)

instance : (pushFunctor (G := G) hf hfe).Additive where
  map_add {P Q f g} := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    obtain ⟨v, rfl⟩ := AsymCat.mkHom_surjective g
    rw [← (Quotient.functor (asymRel G X)).map_add]
    rfl

instance : (pushFunctor (G := G) hf hfe).Linear ℚ where
  map_smul {P Q} f c := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    rw [← (Quotient.functor (asymRel G X)).map_smul]
    rfl

/-- The pushforward `f_* : 𝒜_𝐆(X) → 𝒜_𝐆(X')`, `(n_i, x_i) ↦ (n_i, f ∘ x_i)`, `[u] ↦ [u]`, a
duality functor with `ξ = id`. -/
def push : DualFunctor (AsymCat G X) (AsymCat G X') where
  toFunctor := pushFunctor hf hfe
  ξ _ := Iso.refl _
  ξ_natural f := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  ξ_dual _ := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]
    exact DualCat.dualHom_id _

/-- The pushforward is a strict duality functor. -/
theorem push_isStrict : (push (G := G) hf hfe).IsStrict := fun _ => ⟨rfl, rfl⟩

end HSP

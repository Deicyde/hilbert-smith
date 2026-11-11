import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality
import HilbertSmithPaper.Categories.Asymptotic.PointQuotient

/-!
# Forgetting labels

`Φ : 𝒜_𝐆(X) → 𝒱_𝐆` is the strict duality functor `(n_i, x_i) ↦ (n_i)`, `[u] ↦ q(u_i)`, into the
point category.

Lean encoding. On sequences, `HSP.AsymPre.forgetLabels : AsymPre G X ⥤ PCat G` keeps the
matrices (the bases of `(n_i, x_i)` and `(n_i)` are the same free `G_i`-sets). Composed with the
quotient functor `q`, eventually equal sequences have the same image (they differ in finitely many
coordinates, `HSP.VCat.map_eq_iff`, which rests on the point ideal), so it descends to
`𝒜_𝐆(X)` (`CategoryTheory.Quotient.lift`). `HSP.forgetLabels` is the resulting duality functor,
with `ξ = id`; it is strict (`HSP.forgetLabels_isStrict`).
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- Forgetting the labels on sequences: `(n_i, x_i) ↦ (n_i)`, `u ↦ (u_i)`. -/
@[simps]
def AsymPre.forgetLabels : AsymPre G X ⥤ PCat G where
  obj M := fun i => M.free i
  map u := fun i => AsymPre.coord u i
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem forgetLabels_resp ⦃M N : AsymPre G X⦄ (u v : M ⟶ N) (h : asymRel G X u v) :
    (AsymPre.forgetLabels ⋙ FiltQuot.functor (SCat G)).map u =
      (AsymPre.forgetLabels ⋙ FiltQuot.functor (SCat G)).map v := by
  refine (VCat.map_eq_iff _ _).2 ?_
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h
  refine (Set.finite_lt_nat N₀).subset fun i hi => ?_
  by_contra hlt
  exact hi (hN₀ i (not_lt.1 hlt))

/-- The underlying functor of forgetting labels, `𝒜_𝐆(X) ⥤ 𝒱_𝐆`. -/
def forgetLabelsFunctor : AsymCat G X ⥤ VCat G :=
  CategoryTheory.Quotient.lift (asymRel G X) (AsymPre.forgetLabels ⋙ FiltQuot.functor (SCat G))
    forgetLabels_resp

private theorem forgetLabelsFunctor_map_mkHom {M N : AsymPre G X} (u : M ⟶ N) :
    forgetLabelsFunctor.map (AsymCat.mkHom u) =
      (FiltQuot.functor (SCat G)).map (AsymPre.forgetLabels.map u) := rfl

instance : (forgetLabelsFunctor (G := G) (X := X)).Additive where
  map_add {P Q f g} := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    obtain ⟨v, rfl⟩ := AsymCat.mkHom_surjective g
    rw [← (Quotient.functor (asymRel G X)).map_add]
    rfl

instance : (forgetLabelsFunctor (G := G) (X := X)).Linear ℚ where
  map_smul {P Q} f c := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    rw [← (Quotient.functor (asymRel G X)).map_smul]
    rfl

/-- Forgetting labels, `Φ : 𝒜_𝐆(X) → 𝒱_𝐆`, `(n_i, x_i) ↦ (n_i)`, `[u] ↦ q(u_i)`, a duality
functor with `ξ = id`. -/
def forgetLabels : DualFunctor (AsymCat G X) (VCat G) where
  toFunctor := forgetLabelsFunctor
  ξ _ := Iso.refl _
  ξ_natural f := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  ξ_dual _ := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]
    exact DualCat.dualHom_id _

/-- Forgetting labels is a strict duality functor. -/
theorem forgetLabels_isStrict : (forgetLabels (G := G) (X := X)).IsStrict :=
  fun _ => ⟨rfl, rfl⟩

end HSP

import HilbertSmithPaper.Categories.Supports.SupportDualAdditive
import HilbertSmithPaper.LTheory.Base.Categories.FiltrationQuotient
import HilbertSmithPaper.LTheory.Base.Categories.QuotientDualityFunctor

/-!
# Exterior quotient

For `Z ⊆ X`, the exterior quotient `ℬ_{𝐆,Z}(X) = 𝒜_𝐆(X)/𝒜_Z` (`HSP.Ext G X Z`) is the quotient of
the asymptotic category by its support subcategory `𝒜_Z`, a full additive subcategory closed under
duality (`HSP.isDualAdditive_supp`). It is an `abbrev` for `FiltQuot (supp Z)`, so it carries the
duality category structure of the quotient, and the quotient functor `q = FiltQuot.q (supp Z)` is
a strict duality functor. Closedness and invariance of `Z` are not needed for the definition.
-/

namespace HSP

variable {p : ℕ}

/-- The *exterior quotient* `ℬ_{𝐆,Z}(X) = 𝒜_𝐆(X)/𝒜_Z`. -/
abbrev Ext (G : GroupSeq p) (X : Type*) [MetricSpace X] [AddAction (ZMod p) X] (Z : Set X) :=
  FiltQuot (supp Z : CategoryTheory.ObjectProperty (AsymCat G X))

/-- The trivial action of `C_2` on a point (for the non-vacuity witness). -/
private abbrev unitAction : AddAction (ZMod 2) Unit where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

attribute [local instance] unitAction

open CategoryTheory CategoryTheory.Limits Filter in
/-- Non-vacuity: in `ℬ_{𝟏,∅}(pt)` (`X` a point, `p = 2`), the object with one generator at every
level is not a zero object. -/
private theorem ext_nonvacuous :
    ¬ IsZero ((FiltQuot.functor (supp (∅ : Set Unit))).obj
      (⟨⟨fun _ => 1, fun _ _ => ()⟩⟩ : AsymCat (GroupSeq.trivial 2) Unit)) := by
  intro h
  have h1 := (IsZero.iff_id_eq_zero _).1 h
  rw [← (FiltQuot.functor _).map_id, ← (FiltQuot.functor _).map_zero,
    FiltQuot.functor_map_eq_iff, sub_zero] at h1
  obtain ⟨V, hV, a, b, hab⟩ := h1
  obtain ⟨a, rfl⟩ := AsymCat.mkHom_surjective a
  obtain ⟨b, rfl⟩ := AsymCat.mkHom_surjective b
  rw [← Functor.map_comp] at hab
  have hab' : (Quotient.functor (asymRel (GroupSeq.trivial 2) Unit)).map
      (𝟙 (⟨fun _ => 1, fun _ _ => ()⟩ : AsymPre (GroupSeq.trivial 2) Unit)) =
      (Quotient.functor (asymRel _ _)).map (a ≫ b) :=
    (CategoryTheory.Functor.map_id _ _).trans hab
  replace hab' := (AsymCat.mkHom_eq_iff _ _).1 hab'
  have hn : ∀ᶠ i in atTop, V.as.n i = 0 := (hV 1 one_pos).mono fun i hi => by
    by_contra hn
    have := hi ⟨0, Nat.pos_of_ne_zero hn⟩
    rw [Metric.thickening_empty] at this
    exact this
  obtain ⟨i, hi, hni⟩ := (hab'.and hn).exists
  have hm := congrArg FreeCat.mat hi
  rw [AsymPre.coord_comp, AsymPre.coord_id, FreeCat.mat_comp, FreeCat.mat_id] at hm
  have : IsEmpty ((GroupSeq.trivial 2).G i × Fin (V.as.free i).n) :=
    ⟨fun x => (Fin.cast (by exact hni) x.2).elim0⟩
  have h2 := congrFun (congrFun hm ((), ⟨0, Nat.one_pos⟩)) ((), ⟨0, Nat.one_pos⟩)
  rw [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Matrix.one_apply_eq] at h2
  exact one_ne_zero h2

end HSP

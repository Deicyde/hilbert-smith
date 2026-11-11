import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.EventuallyZeroSubcategory

/-!
# Point ideal

A morphism `(u_i) : M → M'` of the sequence category factors through an object of the
finite-support subcategory `𝒮_𝐆` if and only if `u_i = 0` for all but finitely many `i`.

(⇒) Through `V` with `V_i = 0` outside a finite set, `u_i` factors through the zero object there.
(⇐) If `u_i = 0` outside a finite set, `u` factors through the object that is `M_i` where
`u_i ≠ 0` and `0` elsewhere.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ} {G : GroupSeq p}

/-- The point ideal: `(u_i)` factors through an object of `𝒮_𝐆` iff `u_i = 0` for all but
finitely many `i`. -/
theorem SCat.ideal_iff {M N : PCat G} (u : M ⟶ N) :
    (∃ V : PCat G, SCat G V ∧ ∃ (v : M ⟶ V) (w : V ⟶ N), u = v ≫ w) ↔
      {i | PCat.homCoord u i ≠ 0}.Finite := by
  classical
  constructor
  · rintro ⟨V, hV, v, w, rfl⟩
    refine hV.subset fun i hi => ?_
    intro h0
    apply hi
    rw [PCat.homCoord_comp, (FreeCat.isZero_of_n_eq_zero _ h0).eq_zero_of_src (PCat.homCoord w i),
      Limits.comp_zero]
  · intro hu
    let V : PCat G := fun i =>
      (⟨if PCat.homCoord u i = 0 then 0 else (M.coord i).n⟩ : FreeCat (G.G i))
    have hM : ∀ i, PCat.homCoord u i ≠ 0 → M.coord i = V.coord i := fun i h => by
      show M.coord i = ⟨if PCat.homCoord u i = 0 then 0 else (M.coord i).n⟩
      rw [ite_eq_right h]
    let v : M ⟶ V := fun i =>
      if h : PCat.homCoord u i = 0 then 0 else eqToHom (hM i h)
    let w : V ⟶ N := fun i =>
      if h : PCat.homCoord u i = 0 then 0 else eqToHom (hM i h).symm ≫ PCat.homCoord u i
    have hv : ∀ i, PCat.homCoord v i =
        if h : PCat.homCoord u i = 0 then 0 else eqToHom (hM i h) := fun _ => rfl
    have hw : ∀ i, PCat.homCoord w i =
        if h : PCat.homCoord u i = 0 then 0 else eqToHom (hM i h).symm ≫ PCat.homCoord u i :=
      fun _ => rfl
    refine ⟨V, hu.subset fun i hi => ?_, v, w, PCat.hom_ext fun i => ?_⟩
    · intro h
      apply hi
      show (if PCat.homCoord u i = 0 then 0 else (M.coord i).n) = 0
      rw [ite_eq_left h]
    · rw [PCat.homCoord_comp, hv, hw]
      by_cases h : PCat.homCoord u i = 0
      · rw [dite_eq_left h, Limits.zero_comp]
        exact h
      · rw [dite_eq_right h, dite_eq_right h,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end HSP

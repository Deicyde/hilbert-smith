import Mathlib

/-!
# Lifting homotopy equivalences to a full subcategory

For a fully faithful additive functor `F`, a chain homotopy equivalence between the images of two
complexes lifts to one between the complexes: chain maps and homotopies lift componentwise. For
the inclusion of a full subcategory, a chain homotopy equivalence between complexes in the
subcategory, taken in the ambient category, lifts to one in the subcategory.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

section Lift

variable {V : Type*} [Category V] [Preadditive V] {W : Type*} [Category W] [Preadditive W]
  (F : V ⥤ W) [F.Additive] [F.Full] [F.Faithful]

/-- Homotopies lift through a fully faithful additive functor. -/
private noncomputable def liftHomotopy {K L : ChainComplex V ℤ} {f g : K ⟶ L}
    (h : Homotopy ((F.mapHomologicalComplex _).map f) ((F.mapHomologicalComplex _).map g)) :
    Homotopy f g where
  hom i j := F.preimage (h.hom i j)
  zero i j w := F.map_injective (by rw [Functor.map_preimage, h.zero i j w, F.map_zero])
  comm i := F.map_injective (by
    have H := h.comm i
    dsimp [dNext, prevD] at H ⊢
    simpa [Functor.map_add, Functor.map_comp] using H)

/-- **Lifting homotopy equivalences to a full subcategory.** Homotopy equivalences lift through a
fully faithful additive functor. -/
noncomputable def liftHomotopyEquiv {K L : ChainComplex V ℤ}
    (e : HomotopyEquiv ((F.mapHomologicalComplex _).obj K) ((F.mapHomologicalComplex _).obj L)) :
    HomotopyEquiv K L where
  hom := (F.mapHomologicalComplex _).preimage e.hom
  inv := (F.mapHomologicalComplex _).preimage e.inv
  homotopyHomInvId := liftHomotopy F ((Homotopy.ofEq (by simp)).trans
    (e.homotopyHomInvId.trans (Homotopy.ofEq (by simp))))
  homotopyInvHomId := liftHomotopy F ((Homotopy.ofEq (by simp)).trans
    (e.homotopyInvHomId.trans (Homotopy.ofEq (by simp))))

end Lift

end HSP

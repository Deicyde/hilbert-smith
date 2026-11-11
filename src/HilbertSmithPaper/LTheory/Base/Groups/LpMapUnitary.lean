import HilbertSmithPaper.LTheory.Base.Groups.UnitaryInvariance

/-!
# Unitary invariance on L^p

If `η : F ≅ G` is a unitary natural isomorphism of duality functors `A → A'`, then
`F_* = G_*` on `L^p_k(A)`. The completion `Kar η` has components
`η_M F(e) : (F M, F e) → (G M, G e)` with inverses `η_M⁻¹ G(e)`; it is natural because `η` is, and
unitary because `η` is and `η_M F(e) = G(e) η_M`. Conclude by unitary invariance.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

variable {F G : DualFunctor A A'}

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [Preadditive A']
  [Linear ℚ A'] [HasFiniteBiproducts A'] [DualCat A'] in
private lemma comm_aux {F G : A ⥤ A'} (α : F ⟶ G) (P : Karoubi A) :
    F.map P.p ≫ (F.map P.p ≫ α.app P.X) ≫ G.map P.p = F.map P.p ≫ α.app P.X := by
  rw [Category.assoc, ← α.naturality]
  simp only [← Category.assoc, ← F.map_comp, P.idem]

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [Preadditive A']
  [Linear ℚ A'] [HasFiniteBiproducts A'] [DualCat A'] in
private lemma inv_aux {F G : A ⥤ A'} (α : F ≅ G) (P : Karoubi A) :
    (F.map P.p ≫ α.hom.app P.X) ≫ G.map P.p ≫ α.inv.app P.X = F.map P.p := by
  rw [Category.assoc, ← Category.assoc (α.hom.app P.X), ← α.hom.naturality, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id, ← F.map_comp, P.idem]

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] [Preadditive A']
  [Linear ℚ A'] [HasFiniteBiproducts A'] [DualCat A'] in
private lemma nat_aux {F G : A ⥤ A'} (α : F ⟶ G) {P Q : Karoubi A} (f : P ⟶ Q) :
    F.map f.f ≫ F.map Q.p ≫ α.app Q.X = (F.map P.p ≫ α.app P.X) ≫ G.map f.f := by
  rw [← Category.assoc, ← F.map_comp, Idempotents.Karoubi.comp_p, Category.assoc,
    ← α.naturality, ← Category.assoc, ← F.map_comp, Idempotents.Karoubi.p_comp]

private lemma unitary_aux (η : DualFunctor.UnitaryIso F G) (P : Karoubi A) :
    (F.toFunctor.map (dualHom P.p) ≫ η.iso.hom.app (dual P.X)) ≫
        (G.toFunctor.map (dualHom P.p) ≫ (G.ξ P.X).hom) ≫
          dualHom (F.toFunctor.map P.p ≫ η.iso.hom.app P.X) =
      F.toFunctor.map (dualHom P.p) ≫ (F.ξ P.X).hom := by
  have hid : dualHom (F.toFunctor.map P.p) ≫ dualHom (F.toFunctor.map P.p) =
      dualHom (F.toFunctor.map P.p) := by
    rw [← dualHom_comp, ← F.toFunctor.map_comp, P.idem]
  have hu : ∀ {Z : A'} (g : dual (F.toFunctor.obj P.X) ⟶ Z),
      η.iso.hom.app (dual P.X) ≫ (G.ξ P.X).hom ≫ dualHom (η.iso.hom.app P.X) ≫ g =
        (F.ξ P.X).hom ≫ g := by
    intro Z g
    rw [← η.unitary P.X]
    simp only [Category.assoc]
  rw [dualHom_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (η.iso.hom.app (dual P.X)) (G.toFunctor.map _), ← η.iso.hom.naturality]
  simp only [Category.assoc]
  rw [hu]
  simp only [← Category.assoc, ← F.toFunctor.map_comp, ← dualHom_comp, P.idem]
  rw [F.ξ_natural, Category.assoc, hid]

/-- `Kar η : Kar F ≅ Kar G`, a unitary natural isomorphism, with components `η_M F(e)`. -/
private def karUnitary (η : DualFunctor.UnitaryIso F G) : DualFunctor.UnitaryIso F.kar G.kar where
  iso := NatIso.ofComponents (fun P =>
    { hom := ⟨F.toFunctor.map P.p ≫ η.iso.hom.app P.X, comm_aux η.iso.hom P⟩
      inv := ⟨G.toFunctor.map P.p ≫ η.iso.inv.app P.X, comm_aux η.iso.inv P⟩
      hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (inv_aux η.iso P)
      inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (inv_aux η.iso.symm P) })
    (fun f => Idempotents.Karoubi.hom_ext _ _ (nat_aux η.iso.hom f))
  unitary P := Idempotents.Karoubi.hom_ext _ _ (unitary_aux η P)

/-- If `η : F ≅ G` is a unitary natural isomorphism, then `F_* = G_*` on `L^p_k(A)`. -/
theorem Lp.map_eq_of_unitaryIso (η : DualFunctor.UnitaryIso F G) (k : ℤ) :
    Lp.map F k = Lp.map G k :=
  LGroup.map_eq_of_unitaryIso (karUnitary η) k

end HSP

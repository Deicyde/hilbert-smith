import HilbertSmithPaper.LTheory.Base.Categories.Sums.DualityFunctorSum
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDiag
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctor
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedFunctorIter

/-!
# Bounded extension of a sum of functors

For duality functors `F, G : A → B` there are unitary natural isomorphisms
`σ_j : C_{ℤ^j}(F ⊕ G) ≅ C_{ℤ^j} F ⊕ C_{ℤ^j} G`: `σ_0` is the identity, and `σ_{j+1}` has at
`M = (M_n)_n` the diagonal matrices with entries `π (σ_j)_{M_n}` and `π' (σ_j)_{M_n}` into the
two summands.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v₁ v₂ u₁ u₂

namespace Bounded

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {A' : Type u₂} [Category.{v₂} A'] [Preadditive A'] [Linear ℚ A'] [HasFiniteBiproducts A']
  [DualCat A']

variable {P F G : DualFunctor A A'}

/-- The component `π σ_M : P M → F M` of `σ : P ≅ F ⊕ G`. -/
private abbrev fstσ (σ : DualFunctor.UnitaryIso P (F.biprod G)) (M : A) :
    P.toFunctor.obj M ⟶ F.toFunctor.obj M :=
  σ.iso.hom.app M ≫ (biprod.fst : F.toFunctor.obj M ⊞ G.toFunctor.obj M ⟶ _)

/-- The component `π' σ_M : P M → G M` of `σ : P ≅ F ⊕ G`. -/
private abbrev sndσ (σ : DualFunctor.UnitaryIso P (F.biprod G)) (M : A) :
    P.toFunctor.obj M ⟶ G.toFunctor.obj M :=
  σ.iso.hom.app M ≫ (biprod.snd : F.toFunctor.obj M ⊞ G.toFunctor.obj M ⟶ _)

/-- The component `σ_M⁻¹ ι : F M → P M`. -/
private abbrev inlσ (σ : DualFunctor.UnitaryIso P (F.biprod G)) (M : A) :
    F.toFunctor.obj M ⟶ P.toFunctor.obj M :=
  (biprod.inl : _ ⟶ F.toFunctor.obj M ⊞ G.toFunctor.obj M) ≫ σ.iso.inv.app M

/-- The component `σ_M⁻¹ ι' : G M → P M`. -/
private abbrev inrσ (σ : DualFunctor.UnitaryIso P (F.biprod G)) (M : A) :
    G.toFunctor.obj M ⟶ P.toFunctor.obj M :=
  (biprod.inr : _ ⟶ F.toFunctor.obj M ⊞ G.toFunctor.obj M) ≫ σ.iso.inv.app M

private lemma lift_fstσ_sndσ (σ : DualFunctor.UnitaryIso P (F.biprod G)) (M : A) :
    biprod.lift (fstσ σ M) (sndσ σ M) = σ.iso.hom.app M := by
  apply biprod.hom_ext
  · exact biprod.lift_fst _ _
  · exact biprod.lift_snd _ _

omit [Linear ℚ A'] [DualCat A'] in
private lemma total_aux {X Y Z : A'} (u : Z ≅ X ⊞ Y) :
    (u.hom ≫ biprod.fst) ≫ (biprod.inl ≫ u.inv) + (u.hom ≫ biprod.snd) ≫ (biprod.inr ≫ u.inv) =
      𝟙 Z := by
  rw [Category.assoc, Category.assoc, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
    ← Preadditive.comp_add, ← Preadditive.add_comp, biprod.total, Category.id_comp,
    Iso.hom_inv_id]

omit [Linear ℚ A'] [DualCat A'] in
private lemma inl_fst_aux {X Y Z : A'} (u : Z ≅ X ⊞ Y) :
    (biprod.inl ≫ u.inv) ≫ (u.hom ≫ biprod.fst) = 𝟙 X := by
  simp

omit [Linear ℚ A'] [DualCat A'] in
private lemma inl_snd_aux {X Y Z : A'} (u : Z ≅ X ⊞ Y) :
    (biprod.inl ≫ u.inv) ≫ (u.hom ≫ biprod.snd) = 0 := by
  simp

omit [Linear ℚ A'] [DualCat A'] in
private lemma inr_fst_aux {X Y Z : A'} (u : Z ≅ X ⊞ Y) :
    (biprod.inr ≫ u.inv) ≫ (u.hom ≫ biprod.fst) = 0 := by
  simp

omit [Linear ℚ A'] [DualCat A'] in
private lemma inr_snd_aux {X Y Z : A'} (u : Z ≅ X ⊞ Y) :
    (biprod.inr ≫ u.inv) ≫ (u.hom ≫ biprod.snd) = 𝟙 Y := by
  simp

/-- The isomorphism `C_ℤ P (M) ≅ C_ℤ F (M) ⊕ C_ℤ G (M)` with diagonal components. -/
private def stepIso (σ : DualFunctor.UnitaryIso P (F.biprod G)) (M : Bounded A) :
    (map P).toFunctor.obj M ≅ (map F).toFunctor.obj M ⊞ (map G).toFunctor.obj M where
  hom := biprod.lift
    (diag (M := (map P).toFunctor.obj M) (N := (map F).toFunctor.obj M) fun n => fstσ σ (M.X n))
    (diag (M := (map P).toFunctor.obj M) (N := (map G).toFunctor.obj M) fun n => sndσ σ (M.X n))
  inv := biprod.desc
    (diag (M := (map F).toFunctor.obj M) (N := (map P).toFunctor.obj M) fun n => inlσ σ (M.X n))
    (diag (M := (map G).toFunctor.obj M) (N := (map P).toFunctor.obj M) fun n => inrσ σ (M.X n))
  hom_inv_id := by
    rw [biprod.lift_desc]
    refine ((congrArg₂ (· + ·) (diag_comp_diag _ _) (diag_comp_diag _ _)).trans
      (diag_add _ _)).trans ?_
    refine Eq.trans ?_ (id_eq_diag _).symm
    congr 1
    funext n
    exact total_aux (σ.iso.app (M.X n))
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.lift_fst, biprod.lift_snd,
        Category.assoc, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
        Category.comp_id]
    · refine (diag_comp_diag _ _).trans ?_
      congr 1
      funext n
      exact inl_fst_aux (σ.iso.app (M.X n))
    · refine ((diag_comp_diag _ _).trans ?_).trans diag_zero
      congr 1
      funext n
      exact inl_snd_aux (σ.iso.app (M.X n))
    · refine ((diag_comp_diag _ _).trans ?_).trans diag_zero
      congr 1
      funext n
      exact inr_fst_aux (σ.iso.app (M.X n))
    · refine (diag_comp_diag _ _).trans ?_
      congr 1
      funext n
      exact inr_snd_aux (σ.iso.app (M.X n))

private lemma fstσ_natural (σ : DualFunctor.UnitaryIso P (F.biprod G)) {X Y : A} (g : X ⟶ Y) :
    P.toFunctor.map g ≫ fstσ σ Y = fstσ σ X ≫ F.toFunctor.map g := by
  have h := σ.iso.hom.naturality g
  calc P.toFunctor.map g ≫ σ.iso.hom.app Y ≫ biprod.fst
      = (P.toFunctor.map g ≫ σ.iso.hom.app Y) ≫ biprod.fst := (Category.assoc _ _ _).symm
    _ = (σ.iso.hom.app X ≫ (F.biprod G).toFunctor.map g) ≫ biprod.fst := by rw [h]
    _ = σ.iso.hom.app X ≫ (biprod.map (F.toFunctor.map g) (G.toFunctor.map g) ≫ biprod.fst) :=
      Category.assoc _ _ _
    _ = σ.iso.hom.app X ≫ (biprod.fst ≫ F.toFunctor.map g) :=
      congrArg (fun t => σ.iso.hom.app X ≫ t) (biprod.map_fst _ _)
    _ = (σ.iso.hom.app X ≫ biprod.fst) ≫ F.toFunctor.map g := (Category.assoc _ _ _).symm

private lemma sndσ_natural (σ : DualFunctor.UnitaryIso P (F.biprod G)) {X Y : A} (g : X ⟶ Y) :
    P.toFunctor.map g ≫ sndσ σ Y = sndσ σ X ≫ G.toFunctor.map g := by
  have h := σ.iso.hom.naturality g
  calc P.toFunctor.map g ≫ σ.iso.hom.app Y ≫ biprod.snd
      = (P.toFunctor.map g ≫ σ.iso.hom.app Y) ≫ biprod.snd := (Category.assoc _ _ _).symm
    _ = (σ.iso.hom.app X ≫ (F.biprod G).toFunctor.map g) ≫ biprod.snd := by rw [h]
    _ = σ.iso.hom.app X ≫ (biprod.map (F.toFunctor.map g) (G.toFunctor.map g) ≫ biprod.snd) :=
      Category.assoc _ _ _
    _ = σ.iso.hom.app X ≫ (biprod.snd ≫ G.toFunctor.map g) :=
      congrArg (fun t => σ.iso.hom.app X ≫ t) (biprod.map_snd _ _)
    _ = (σ.iso.hom.app X ≫ biprod.snd) ≫ G.toFunctor.map g := (Category.assoc _ _ _).symm

private lemma entry_unitary (σ : DualFunctor.UnitaryIso P (F.biprod G)) (X : A) :
    fstσ σ (dual X) ≫ (F.ξ X).hom ≫ dualHom (fstσ σ X) +
      sndσ σ (dual X) ≫ (G.ξ X).hom ≫ dualHom (sndσ σ X) = (P.ξ X).hom := by
  have h := DualFunctor.lift_biprod_ξ_dualHom_lift F G X (fstσ σ (dual X)) (sndσ σ (dual X))
    (fstσ σ X) (sndσ σ X)
  rw [lift_fstσ_sndσ, lift_fstσ_sndσ] at h
  exact h.symm.trans (σ.unitary X)

/-- One level: `σ : P ≅ F ⊕ G` gives `C_ℤ P ≅ C_ℤ F ⊕ C_ℤ G`. -/
private def stepUnitary (σ : DualFunctor.UnitaryIso P (F.biprod G)) :
    DualFunctor.UnitaryIso (map P) ((map F).biprod (map G)) where
  iso := NatIso.ofComponents (stepIso σ) (fun {M N} f => by
    change (map P).toFunctor.map f ≫ biprod.lift
        (diag (M := (map P).toFunctor.obj N) (N := (map F).toFunctor.obj N)
          fun n => fstσ σ (N.X n))
        (diag (M := (map P).toFunctor.obj N) (N := (map G).toFunctor.obj N)
          fun n => sndσ σ (N.X n)) =
      biprod.lift
        (diag (M := (map P).toFunctor.obj M) (N := (map F).toFunctor.obj M)
          fun n => fstσ σ (M.X n))
        (diag (M := (map P).toFunctor.obj M) (N := (map G).toFunctor.obj M)
          fun n => sndσ σ (M.X n)) ≫
        biprod.map ((map F).toFunctor.map f) ((map G).toFunctor.map f)
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, Category.assoc, biprod.map_fst, ← Category.assoc,
        biprod.lift_fst]
      exact hom_ext fun a b =>
        (compF_diagF (M := ⟨fun n => P.toFunctor.obj (M.X n)⟩)
          (N := ⟨fun n => P.toFunctor.obj (N.X n)⟩) (P := ⟨fun n => F.toFunctor.obj (N.X n)⟩)
          (fun m n => P.toFunctor.map (f.1 m n)) (fun n => fstσ σ (N.X n)) a b).trans
        ((fstσ_natural σ (f.1 a b)).trans
          (diagF_compF (M := ⟨fun n => P.toFunctor.obj (M.X n)⟩)
            (N := ⟨fun n => F.toFunctor.obj (M.X n)⟩) (P := ⟨fun n => F.toFunctor.obj (N.X n)⟩)
            (fun n => fstσ σ (M.X n)) (fun m n => F.toFunctor.map (f.1 m n)) a b).symm)
    · rw [Category.assoc, biprod.lift_snd, Category.assoc, biprod.map_snd, ← Category.assoc,
        biprod.lift_snd]
      exact hom_ext fun a b =>
        (compF_diagF (M := ⟨fun n => P.toFunctor.obj (M.X n)⟩)
          (N := ⟨fun n => P.toFunctor.obj (N.X n)⟩) (P := ⟨fun n => G.toFunctor.obj (N.X n)⟩)
          (fun m n => P.toFunctor.map (f.1 m n)) (fun n => sndσ σ (N.X n)) a b).trans
        ((sndσ_natural σ (f.1 a b)).trans
          (diagF_compF (M := ⟨fun n => P.toFunctor.obj (M.X n)⟩)
            (N := ⟨fun n => G.toFunctor.obj (M.X n)⟩) (P := ⟨fun n => G.toFunctor.obj (N.X n)⟩)
            (fun n => sndσ σ (M.X n)) (fun m n => G.toFunctor.map (f.1 m n)) a b).symm))
  unitary M := by
    change biprod.lift
        (diag (M := (map P).toFunctor.obj (dual M)) (N := (map F).toFunctor.obj (dual M))
          fun n => fstσ σ ((dual M).X n))
        (diag (M := (map P).toFunctor.obj (dual M)) (N := (map G).toFunctor.obj (dual M))
          fun n => sndσ σ ((dual M).X n)) ≫
      (((map F).biprod (map G)).ξ M).hom ≫ dualHom (biprod.lift
        (diag (M := (map P).toFunctor.obj M) (N := (map F).toFunctor.obj M)
          fun n => fstσ σ (M.X n))
        (diag (M := (map P).toFunctor.obj M) (N := (map G).toFunctor.obj M)
          fun n => sndσ σ (M.X n))) = _
    rw [DualFunctor.lift_biprod_ξ_dualHom_lift, map_ξ_hom, map_ξ_hom, map_ξ_hom]
    erw [dualHom_diag_eq, dualHom_diag_eq, diag_comp_diag, diag_comp_diag, diag_comp_diag,
      diag_comp_diag, diag_add]
    congr 1
    funext n
    exact entry_unitary σ (M.X n)

/-- **Bounded extension of a sum of functors**: the unitary natural isomorphisms
`σ_j : C_{ℤ^j}(F ⊕ G) ≅ C_{ℤ^j} F ⊕ C_{ℤ^j} G`, with `σ_0` the identity. -/
def sumIsoIter (F G : DualFunctor A A') :
    ∀ j : ℕ, DualFunctor.UnitaryIso (mapIter (F.biprod G) j) ((mapIter F j).biprod (mapIter G j))
  | 0 => DualFunctor.UnitaryIso.refl (F.biprod G)
  | j + 1 => stepUnitary (sumIsoIter F G j)

end Bounded

end HSP

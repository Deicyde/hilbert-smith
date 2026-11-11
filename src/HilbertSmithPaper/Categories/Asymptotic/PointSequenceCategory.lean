import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Sequence category

For a group sequence `𝐆 = (G_i, χ_i)`, the duality category `𝒫_𝐆 = ∏_i Free(ℚ[G_i])`
(`HSP.PCat G`): objects are sequences `(n_i)` of objects of `Free(ℚ[G_i])`, morphisms are sequences
`(u_i)` of morphisms, and composition, identities, sums and the duality `(n_i)^* = (n_i)`,
`(u_i)^* = (u_iᵀ)` are taken coordinatewise. The coordinate functors
`π_i : 𝒫_𝐆 → Free(ℚ[G_i])` (`HSP.PCat.proj`) are strict duality functors. Only the groups `G_i`
enter, not the `χ_i`.

Lean encoding. `PCat G` is a type synonym of `∀ i, FreeCat (G.G i)` carrying Mathlib's product
category structure (`CategoryTheory.pi`); the preadditive, `ℚ`-linear, biproduct and duality
structures are defined here coordinatewise (Mathlib has no preadditive structure on product
categories). The biproduct of `(n_i)` and `(m_i)` is `(n_i + m_i)` with the coordinate
inclusions and projections of `Free(ℚ[G_i])`, and the zero object is the zero sequence.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ}

/-- The sequence category `𝒫_𝐆 = ∏_i Free(ℚ[G_i])`. -/
def PCat (G : GroupSeq p) : Type := ∀ i, FreeCat (G.G i)

namespace PCat

variable {G : GroupSeq p}

instance : Category (PCat G) := inferInstanceAs (Category (∀ i, FreeCat (G.G i)))

/-- The coordinate `n_i` of an object. -/
def coord (X : PCat G) (i : ℕ) : FreeCat (G.G i) := X i

/-- The coordinate `u_i` of a morphism. -/
def homCoord {X Y : PCat G} (f : X ⟶ Y) (i : ℕ) : X.coord i ⟶ Y.coord i := f i

@[ext]
theorem hom_ext {X Y : PCat G} {f g : X ⟶ Y} (h : ∀ i, homCoord f i = homCoord g i) : f = g :=
  funext h

@[simp] theorem homCoord_id (X : PCat G) (i : ℕ) : homCoord (𝟙 X) i = 𝟙 (X.coord i) := rfl

@[simp] theorem homCoord_comp {X Y Z : PCat G} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℕ) :
    homCoord (f ≫ g) i = homCoord f i ≫ homCoord g i := rfl

instance (X Y : PCat G) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (∀ i, X.coord i ⟶ Y.coord i))

instance (X Y : PCat G) : Module ℚ (X ⟶ Y) :=
  inferInstanceAs (Module ℚ (∀ i, X.coord i ⟶ Y.coord i))

@[simp] theorem homCoord_add {X Y : PCat G} (f g : X ⟶ Y) (i : ℕ) :
    homCoord (f + g) i = homCoord f i + homCoord g i := rfl
@[simp] theorem homCoord_zero {X Y : PCat G} (i : ℕ) : homCoord (0 : X ⟶ Y) i = 0 := rfl
@[simp] theorem homCoord_neg {X Y : PCat G} (f : X ⟶ Y) (i : ℕ) :
    homCoord (-f) i = -homCoord f i := rfl
@[simp] theorem homCoord_sub {X Y : PCat G} (f g : X ⟶ Y) (i : ℕ) :
    homCoord (f - g) i = homCoord f i - homCoord g i := rfl
@[simp] theorem homCoord_smul {X Y : PCat G} (c : ℚ) (f : X ⟶ Y) (i : ℕ) :
    homCoord (c • f) i = c • homCoord f i := rfl

instance : Preadditive (PCat G) where
  add_comp _ _ _ f f' g := hom_ext fun i => by
    simp only [homCoord_comp, homCoord_add, Preadditive.add_comp]
  comp_add _ _ _ f g g' := hom_ext fun i => by
    simp only [homCoord_comp, homCoord_add, Preadditive.comp_add]

instance : Linear ℚ (PCat G) where
  smul_comp _ _ _ c f g := hom_ext fun i => by
    simp only [homCoord_comp, homCoord_smul, Linear.smul_comp]
  comp_smul _ _ _ f c g := hom_ext fun i => by
    simp only [homCoord_comp, homCoord_smul, Linear.comp_smul]

/-- The coordinatewise binary biproduct `(n_i + m_i)`, with the coordinate inclusions and
projections of `Free(ℚ[G_i])`. -/
def binaryBicone (X Y : PCat G) : BinaryBicone X Y where
  pt := fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).pt
  fst := fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).fst
  snd := fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).snd
  inl := fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).inl
  inr := fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).inr
  inl_fst := hom_ext fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).inl_fst
  inl_snd := hom_ext fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).inl_snd
  inr_fst := hom_ext fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).inr_fst
  inr_snd := hom_ext fun i => (FreeCat.binaryBicone (X.coord i) (Y.coord i)).inr_snd

theorem binaryBicone_total (X Y : PCat G) :
    (binaryBicone X Y).fst ≫ (binaryBicone X Y).inl +
      (binaryBicone X Y).snd ≫ (binaryBicone X Y).inr = 𝟙 (binaryBicone X Y).pt :=
  hom_ext fun i => FreeCat.binaryBicone_total (X.coord i) (Y.coord i)

/-- The zero sequence is a zero object. -/
theorem isZero_zero : IsZero (fun _ => ⟨0⟩ : PCat G) :=
  ⟨fun _ => ⟨⟨⟨fun _ => 0⟩, fun _ => funext fun i =>
      (FreeCat.isZero_zero (G := G.G i)).eq_of_src _ _⟩⟩,
    fun _ => ⟨⟨⟨fun _ => 0⟩, fun _ => funext fun i =>
      (FreeCat.isZero_zero (G := G.G i)).eq_of_tgt _ _⟩⟩⟩

instance : HasZeroObject (PCat G) := isZero_zero.hasZeroObject

instance : HasBinaryBiproducts (PCat G) :=
  ⟨fun X Y => hasBinaryBiproduct_of_total (binaryBicone X Y) (binaryBicone_total X Y)⟩

instance : HasFiniteBiproducts (PCat G) := by
  have := hasFiniteProducts_of_has_binary_and_terminal (C := PCat G)
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- `𝒫_𝐆` is a strict duality category under `(n_i)^* = (n_i)` and `(u_i)^* = (u_iᵀ)`. -/
instance dualCat : DualCat (PCat G) where
  dual X := X
  dualHom f := fun i => DualCat.dualHom (f i)
  dualHom_id X := hom_ext fun i => DualCat.dualHom_id (X.coord i)
  dualHom_comp f g := hom_ext fun i => DualCat.dualHom_comp (f i) (g i)
  dualHom_add f g := hom_ext fun i => DualCat.dualHom_add (f i) (g i)
  dualHom_smul c f := hom_ext fun i => DualCat.dualHom_smul c (f i)
  dual_dual _ := rfl
  dualHom_dualHom f := funext fun i =>
    FreeCat.hom_ext (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
      FreeCat.mat_dualHom, Matrix.transpose_transpose])
  dualHom_zero := hom_ext fun _ => DualCat.dualHom_zero
  dualHom_neg f := hom_ext fun i => DualCat.dualHom_neg (f i)
  dualHom_sub f g := hom_ext fun i => DualCat.dualHom_sub (f i) (g i)
  dualHom_eqToHom h := by
    subst h
    simp only [eqToHom_refl]
    exact hom_ext fun i => DualCat.dualHom_id _

@[simp] theorem homCoord_dualHom {X Y : PCat G} (f : X ⟶ Y) (i : ℕ) :
    homCoord (DualCat.dualHom f) i = DualCat.dualHom (homCoord f i) := rfl

/-- The coordinate functor `π_i : 𝒫_𝐆 → Free(ℚ[G_i])`. -/
@[simps]
def projFunctor (G : GroupSeq p) (i : ℕ) : PCat G ⥤ FreeCat (G.G i) where
  obj X := X.coord i
  map f := homCoord f i

instance (i : ℕ) : (projFunctor G i).Additive where
instance (i : ℕ) : (projFunctor G i).Linear ℚ where

/-- The coordinate functor `π_i : 𝒫_𝐆 → Free(ℚ[G_i])` as a duality functor, with `ξ = id`. -/
def proj (G : GroupSeq p) (i : ℕ) : DualFunctor (PCat G) (FreeCat (G.G i)) where
  toFunctor := projFunctor G i
  ξ _ := Iso.refl _
  ξ_natural f := by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  ξ_dual M := by simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]; exact DualCat.dualHom_id _

/-- The coordinate functors are strict duality functors. -/
theorem proj_isStrict (G : GroupSeq p) (i : ℕ) : (proj G i).IsStrict :=
  fun _ => ⟨rfl, rfl⟩

end PCat

end HSP

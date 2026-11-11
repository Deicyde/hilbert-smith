import HilbertSmithPaper.LTheory.Base.Categories.DualAdditiveSubcategory
import HilbertSmithPaper.LTheory.Localization.Products.BasedVectorSpaces

/-!
# Involution-invariant Karoubi filtration

For a full additive subcategory `𝒰 ⊂ 𝒜` closed under duality (`HSP.IsDualAdditive U`, no closure
under isomorphism), an involution-invariant Karoubi filtration chooses for each object `M` a
nonempty directed set `D M` of `𝒰`-decompositions of `M`, satisfying factorization and duality.

Encoding.
* A `𝒰`-decomposition of `M` is an endomorphism `p : M ⟶ M` with `p ≫ p = p`, together with
  splittings (stated as existence): `E` in `𝒰` with `i : E ⟶ M`, `r : M ⟶ E`, `i ≫ r = 𝟙 E`,
  `r ≫ i = p` (the paper's `ri = 1`, `ir = p`, composition written in diagrammatic order), and
  `M'` with `i' ≫ r' = 𝟙 M'`, `r' ≫ i' = 𝟙 M - p`.
* The order `p ≤ p'` (paper: `p'p = p = pp'`) is `p ≫ p' = p ∧ p' ≫ p = p`; directedness is
  stated with it inline.
* Factorization: for `g : V ⟶ M` with `V` in `𝒰`, some `p ∈ D M` has `g ≫ p = g` (paper:
  `pg = g`); for `h : M ⟶ V`, some `p` has `p ≫ h = h` (paper: `hp = h`).
* Duality: `p ∈ D M ↔ p^* ∈ D M^*`.

The chosen decompositions are data, so a filtration is a structure, not a Prop. Compatibility with
sums is not a field; it is a separate lemma (filtrations are compatible with sums).
-/

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace HSP

open DualCat

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- An *involution-invariant Karoubi filtration* of `𝒜` by a full additive subcategory `𝒰`
closed under duality: a nonempty directed set `D M` of `𝒰`-decompositions of each object `M`,
with the factorization and duality properties. -/
structure KaroubiFiltration (U : ObjectProperty A) [IsDualAdditive U] where
  /-- The chosen `𝒰`-decompositions of `M`. -/
  D : ∀ M : A, Set (M ⟶ M)
  /-- Each chosen decomposition is idempotent. -/
  idem {M : A} {p : M ⟶ M} : p ∈ D M → p ≫ p = p
  /-- `p` splits through an object of `𝒰`: `ri = 1`, `ir = p`. -/
  split {M : A} {p : M ⟶ M} : p ∈ D M →
    ∃ (E : A) (_ : U E) (i : E ⟶ M) (r : M ⟶ E), i ≫ r = 𝟙 E ∧ r ≫ i = p
  /-- `1 - p` splits: `r'i' = 1`, `i'r' = 1 - p`. -/
  split_compl {M : A} {p : M ⟶ M} : p ∈ D M →
    ∃ (M' : A) (i' : M' ⟶ M) (r' : M ⟶ M'), i' ≫ r' = 𝟙 M' ∧ r' ≫ i' = 𝟙 M - p
  /-- Each `D M` is nonempty. -/
  nonempty (M : A) : (D M).Nonempty
  /-- Each `D M` is directed for `p ≤ p' ⇔ p'p = p = pp'`. -/
  directed {M : A} {p p' : M ⟶ M} : p ∈ D M → p' ∈ D M →
    ∃ p'' ∈ D M, (p ≫ p'' = p ∧ p'' ≫ p = p) ∧ (p' ≫ p'' = p' ∧ p'' ≫ p' = p')
  /-- Factorization of maps from `𝒰`: `pg = g` for some `p ∈ D M`. -/
  factor_left {V M : A} (g : V ⟶ M) : U V → ∃ p ∈ D M, g ≫ p = g
  /-- Factorization of maps to `𝒰`: `hp = h` for some `p ∈ D M`. -/
  factor_right {M V : A} (h : M ⟶ V) : U V → ∃ p ∈ D M, p ≫ h = h
  /-- Duality: `p ∈ D M ↔ p^* ∈ D M^*`. -/
  dual_mem_iff {M : A} (p : M ⟶ M) : p ∈ D M ↔ dualHom p ∈ D (dual M)

/-- Non-vacuity: all based vector spaces form a dual-closed additive subcategory of `FreeQ`. -/
private theorem isDualAdditive_top : IsDualAdditive (⊤ : ObjectProperty FreeQ) where
  exists_zero := ⟨0, trivial, isZero_zero FreeQ⟩
  exists_biprod {V W} _ _ := by
    have := hasBinaryBiproducts_of_finite_biproducts FreeQ
    exact ⟨BinaryBiproduct.bicone V W, ⟨BinaryBiproduct.isBilimit V W⟩, trivial⟩
  dual_mem _ := trivial

/-- Non-vacuity: the filtration of `FreeQ` by all objects, with `D M = {𝟙 M}`. -/
private noncomputable def karoubiFiltrationTop :
    @KaroubiFiltration FreeQ _ _ _ _ _ ⊤ isDualAdditive_top :=
  @KaroubiFiltration.mk FreeQ _ _ _ _ _ ⊤ isDualAdditive_top (fun M => {𝟙 M})
    (by rintro M p rfl; simp)
    (by rintro M p rfl; exact ⟨M, trivial, 𝟙 M, 𝟙 M, by simp, by simp⟩)
    (by rintro M p rfl; exact ⟨0, 0, 0, (isZero_zero FreeQ).eq_of_src _ _, by simp⟩)
    (fun M => ⟨𝟙 M, rfl⟩)
    (by rintro M p p' rfl rfl; exact ⟨𝟙 M, rfl, by simp⟩)
    (fun g _ => ⟨𝟙 _, rfl, by simp⟩)
    (fun h _ => ⟨𝟙 _, rfl, by simp⟩)
    (fun {M} p => by
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; simp
      · intro h
        have h2 := dualHom_dualHom p
        rw [h, dualHom_id] at h2
        have h3 := congrArg (fun q => eqToHom (dual_dual M).symm ≫ q ≫ eqToHom (dual_dual M)) h2
        simpa using h3.symm)

end HSP

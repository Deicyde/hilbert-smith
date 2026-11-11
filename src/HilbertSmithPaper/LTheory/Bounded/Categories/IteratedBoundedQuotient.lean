import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedQuotient
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSub
import HilbertSmithPaper.LTheory.Bounded.Categories.IteratedBoundedSubAdditive
import HilbertSmithPaper.LTheory.Bounded.BoundedFunctorStrict

/-!
# Iterated bounded quotients

For an involution-invariant Karoubi filtration `F` of `A` by `U`, the iterated bounded quotient
isomorphism `e_j` from the quotient of `C_{ℤ^j}A` by `C_{ℤ^j}U` to `C_{ℤ^j}(A/U)`
(`Bounded.powQuotientIso F j`) is a strict duality functor together with a strict duality functor
inverse to it (both composites are identity functors), bundled as a subtype of pairs. It is
defined by recursion: `e_0 = id`, and `e_{j+1} = C_ℤ(e_j) ∘ ẽ_j` with `ẽ_j` the entrywise
quotient functor of the bounded quotients (for the filtration `C_{ℤ^j}U ⊂ C_{ℤ^j}A`), whose strict
inverse comes from `Bounded.quotientEquiv`; the inverse of `e_{j+1}` is the composite of
`C_ℤ` of the inverse of `e_j` with that inverse.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

section Aux

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B] {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℚ C] [HasFiniteBiproducts C]
  [DualCat C]

omit [HasFiniteBiproducts A] [DualCat A] [HasFiniteBiproducts B] [DualCat B]
  [HasFiniteBiproducts C] [DualCat C] in
private lemma mapFunctor_comp (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] :
    mapFunctor F ⋙ mapFunctor G = mapFunctor (F ⋙ G) := rfl

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma mapFunctor_id : mapFunctor (𝟭 A) = 𝟭 (Bounded A) := rfl

omit [HasFiniteBiproducts A] [DualCat A] [HasFiniteBiproducts B] [DualCat B] in
private lemma mapFunctor_congr {F G : A ⥤ B} [F.Additive] [G.Additive] (h : F = G) :
    mapFunctor F = mapFunctor G := by
  subst h
  rfl

private lemma comp_isStrict {F : DualFunctor A B} {G : DualFunctor B C} (hF : F.IsStrict)
    (hG : G.IsStrict) : (F.comp G).IsStrict := by
  intro M
  obtain ⟨h1, e1⟩ := hF M
  obtain ⟨h2, e2⟩ := hG (F.toFunctor.obj M)
  refine ⟨(congrArg G.toFunctor.obj h1).trans h2, ?_⟩
  show G.toFunctor.map (F.ξ M).hom ≫ (G.ξ (F.toFunctor.obj M)).hom = _
  rw [e1, e2, eqToHom_map, eqToHom_trans]
  rfl

end Aux

variable {U : ObjectProperty A} [IsDualAdditive U]

/-- **Iterated bounded quotients.** The isomorphism of duality categories `e_j` from the quotient
of `C_{ℤ^j}A` by `C_{ℤ^j}U` to `C_{ℤ^j}(A/U)`: a strict duality functor with a strict duality
functor inverse, `e_0 = id`, `e_{j+1} = C_ℤ(e_j) ∘ ẽ_j`. -/
def powQuotientIso (F : KaroubiFiltration U) : ∀ j : ℕ,
    {e : DualFunctor (FiltQuot (subPow U j)) (BoundedPow (FiltQuot U) j) ×
        DualFunctor (BoundedPow (FiltQuot U) j) (FiltQuot (subPow U j)) //
      e.1.IsStrict ∧ e.2.IsStrict ∧ e.1.toFunctor ⋙ e.2.toFunctor = 𝟭 _ ∧
        e.2.toFunctor ⋙ e.1.toFunctor = 𝟭 _}
  | 0 => ⟨(DualFunctor.id (FiltQuot U), DualFunctor.id (FiltQuot U)),
      fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | j + 1 =>
    let e := powQuotientIso F j
    let hG := quotientEquiv (subPow U j) (powKaroubiFiltration F j)
    ⟨((quotientFunctor (subPow U j)).comp (map e.1.1), (map e.1.2).comp hG.choose),
      comp_isStrict (quotientFunctor_isStrict _) (map_isStrict e.2.1),
      comp_isStrict (map_isStrict e.2.2.1) hG.choose_spec.1,
      by
        change (quotientFunctor (subPow U j)).toFunctor ⋙
          (mapFunctor e.1.1.toFunctor ⋙ mapFunctor e.1.2.toFunctor) ⋙ hG.choose.toFunctor = _
        rw [mapFunctor_comp, mapFunctor_congr e.2.2.2.1, mapFunctor_id]
        exact hG.choose_spec.2.1,
      by
        change mapFunctor e.1.2.toFunctor ⋙ (hG.choose.toFunctor ⋙
          (quotientFunctor (subPow U j)).toFunctor) ⋙ mapFunctor e.1.1.toFunctor = _
        rw [hG.choose_spec.2.2, Functor.id_comp, mapFunctor_comp,
          mapFunctor_congr e.2.2.2.2, mapFunctor_id]
        rfl⟩

end Bounded

end HSP

end

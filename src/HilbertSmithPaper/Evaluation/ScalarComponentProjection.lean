import HilbertSmithPaper.Evaluation.ExcisiveIntersectionQuotient
import HilbertSmithPaper.Categories.Supports.Excision
import HilbertSmithPaper.Categories.Supports.QuotientByEmpty
import HilbertSmithPaper.Categories.Functors.RelabellingEquivalence
import HilbertSmithPaper.Categories.Functors.ForgetLabels
import HilbertSmithPaper.Corner.CutFlag
import HilbertSmithPaper.LTheory.Ultimate.Groups.EquivalenceInvariance

/-!
# Scalar component projection

Let `n ≥ 1`, `s > 0`, and let `Y_n = {y_-, y_+}` be the last cut set, with `y_- ≠ y_+`. Over the
round sphere and the trivial group sequence `𝟏`, the scalar component projection
`π_+ : 𝕃_4(𝒜_{Y_n}) → 𝕃_4(𝒱_𝟏)` is the composite of
1. `q_*`, for the quotient functor `q : 𝒜_{Y_n} → 𝒜_{Y_n}/𝒜_{y_-}`;
2. `(e_*)⁻¹`, for the excision equivalence `e : 𝒰_+/(𝒰_+ ∩ 𝒰_-) → 𝒜_{Y_n}/𝒜_{y_-}`, where `𝒰_±`
   are the `y_±`-supported objects of `𝒜_{Y_n}`, followed by the map induced by the identification
   `𝒰_+/(𝒰_+ ∩ 𝒰_-) → 𝒜_{y_+}/𝒜_∅` (`HSP.excisiveInterQuotIso` for `A = {y_+}`, `B = {y_-}`,
   `S = Y_n`, `C = ∅`; `{y_+}` is compact);
3. `(q'_*)⁻¹`, for the quotient isomorphism `q' : 𝒜_{y_+} → 𝒜_{y_+}/𝒜_∅`;
4. `(P_*)⁻¹`, for the inclusion `P : 𝒜_𝟏({y_+}) → 𝒜_{y_+}` of the relabelling equivalence;
5. `Φ_*`, for forgetting labels `Φ : 𝒜_𝟏({y_+}) → 𝒱_𝟏`.
Each inverse is the inverse of an induced isomorphism, by equivalence invariance.

For the quotient isomorphism, the natural isomorphisms of equivalence invariance are identities.
The trivial group sequence is taken for a natural number `p`, which need not be prime.
-/

open CategoryTheory CategoryTheory.Limits Metric

namespace HSP.Evaluation

open Corner DualCat

universe v u

section Aux

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

/-- The isomorphism `F_* : 𝕃_k(A) ≅ 𝕃_k(B)` of equivalence invariance, with inverse `G_*`. -/
private noncomputable def indEquiv (F : DualFunctor A B) (G : DualFunctor B A)
    (η : DualFunctor.UnitaryIso (DualFunctor.id A) (F.comp G))
    (ε : DualFunctor.UnitaryIso (G.comp F) (DualFunctor.id B)) (k : ℤ) :
    ultL A k ≃+ ultL B k :=
  AddMonoidHom.toAddEquiv (ultL.map F k) (ultL.map G k) (ultL.map_inverse F G η ε k).1
    (ultL.map_inverse F G η ε k).2

private lemma comp_isStrict {F : DualFunctor A B} {G : DualFunctor B A} (hF : F.IsStrict)
    (hG : G.IsStrict) : (F.comp G).IsStrict := by
  intro M
  obtain ⟨h1, e1⟩ := hF M
  obtain ⟨h2, e2⟩ := hG (F.toFunctor.obj M)
  refine ⟨(congrArg G.toFunctor.obj h1).trans h2, ?_⟩
  show G.toFunctor.map (F.ξ M).hom ≫ (G.ξ (F.toFunctor.obj M)).hom = _
  rw [e1, e2, eqToHom_map, eqToHom_trans]
  rfl

omit [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
private lemma eqToIso_hom_app {F G : A ⥤ A} (h : F = G) (X : A) :
    (eqToIso h).hom.app X = eqToHom (Functor.congr_obj h X) := by
  subst h
  rfl

/-- The identity natural isomorphism `id = F` of a strict duality functor equal to the identity
is unitary. -/
private def unitaryOfEq {F : DualFunctor A A} (hF : F.IsStrict)
    (h : (DualFunctor.id A).toFunctor = F.toFunctor) :
    DualFunctor.UnitaryIso (DualFunctor.id A) F where
  iso := eqToIso h
  unitary M := by
    obtain ⟨hM, hξ⟩ := hF M
    rw [eqToIso_hom_app, eqToIso_hom_app, hξ, dualHom_eqToHom, eqToHom_trans, eqToHom_trans]
    exact eqToHom_refl _ _

/-- The identity natural isomorphism `F = id` of a strict duality functor equal to the identity
is unitary. -/
private def unitaryOfEq' {F : DualFunctor A A} (hF : F.IsStrict)
    (h : F.toFunctor = (DualFunctor.id A).toFunctor) :
    DualFunctor.UnitaryIso F (DualFunctor.id A) where
  iso := eqToIso h
  unitary M := by
    obtain ⟨hM, hξ⟩ := hF M
    rw [eqToIso_hom_app, eqToIso_hom_app, hξ, dualHom_eqToHom]
    erw [Category.id_comp, eqToHom_trans]

/-- The isomorphism `F_*` for mutually inverse strict duality functors `F` and `G`. -/
private noncomputable def strictEquiv (F : DualFunctor A B) (G : DualFunctor B A)
    (hF : F.IsStrict) (hG : G.IsStrict) (h₁ : F.toFunctor ⋙ G.toFunctor = 𝟭 A)
    (h₂ : G.toFunctor ⋙ F.toFunctor = 𝟭 B) (k : ℤ) : ultL A k ≃+ ultL B k :=
  indEquiv F G (unitaryOfEq (comp_isStrict hF hG) h₁.symm)
    (unitaryOfEq' (comp_isStrict hG hF) h₂) k

end Aux

variable (p : ℕ) (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)

/-- The point `{y_+}` as an invariant subset (the action on the sphere is trivial). -/
private def plusSub : SubAddAction (ZMod p) (RoundSphere n) where
  carrier := {yPlus n s}
  vadd_mem' _ _ hx := hx

include hn hs in
private lemma cut_cover : cutY n s n ⊆ {yPlus n s} ∪ {yMinus n s} := by
  rw [(cut_flag n hn s hs).2.1]
  intro x hx
  rcases hx with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

include hn hs in
private lemma plus_subset : ({yPlus n s} : Set (RoundSphere n)) ⊆ cutY n s n := by
  rw [(cut_flag n hn s hs).2.1]
  exact Set.singleton_subset_iff.2 (Or.inr rfl)

include hn hs in
private lemma plus_inter_minus : ({yPlus n s} : Set (RoundSphere n)) ∩ {yMinus n s} = ∅ :=
  Set.disjoint_iff_inter_eq_empty.1 (Set.disjoint_singleton.2 (cut_flag n hn s hs).2.2.symm)

/-- **The scalar component projection** `π_+ : 𝕃_4(𝒜_{Y_n}) → 𝕃_4(𝒱_𝟏)`. -/
noncomputable def scalarComponentProj :
    ultL (supp (G := GroupSeq.trivial p) (cutY n s n)).FullSubcategory 4 →+
      ultL (VCat (GroupSeq.trivial p)) 4 :=
  let ex := excision (G := GroupSeq.trivial p) (cutY n s n) {yPlus n s} {yMinus n s}
    (cut_cover n hn s hs) fun _ _ hx => hx
  let br := excisiveInterQuotIso (G := GroupSeq.trivial p) (cutY n s n) isCompact_singleton
    isClosed_singleton (plus_subset n hn s hs) (plus_inter_minus n hn s hs)
  let qe := quotientByEmptyIso (G := GroupSeq.trivial p) ({yPlus n s} : Set (RoundSphere n))
  let rel := relabelEquiv (G := GroupSeq.trivial p) (S := plusSub p n s)
    (isClosed_singleton (x := yPlus n s)) (ρ := fun _ => ⟨yPlus n s, rfl⟩)
    (fun x => (infDist_singleton (x := x) (y := yPlus n s)).symm)
  (ultL.map forgetLabels 4).comp <|
    (indEquiv rel.P rel.R rel.unit rel.counit 4).symm.toAddMonoidHom.comp <|
    (strictEquiv qe.1.1 qe.1.2 qe.2.2.1 qe.2.2.2.1 qe.2.2.2.2.1
      qe.2.2.2.2.2 4).symm.toAddMonoidHom.comp <|
    (ultL.map br.1.1 4).comp <|
    (indEquiv (ExcisivePair.e _ _) ex.1 ex.2.1 ex.2.2 4).symm.toAddMonoidHom.comp <|
    ultL.map (FiltQuot.q _) 4

end HSP.Evaluation

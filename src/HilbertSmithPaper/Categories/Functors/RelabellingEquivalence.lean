import Mathlib
import HilbertSmithPaper.Categories.Functors.Pushforward
import HilbertSmithPaper.Categories.Functors.RelabellingIsomorphismNatural
import HilbertSmithPaper.Categories.Functors.RelabellingIsomorphismUnitary
import HilbertSmithPaper.Categories.Supports.SupportDualAdditive
import HilbertSmithPaper.LTheory.Base.Categories.DualSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.UnitaryIsomorphism

/-!
# Relabelling equivalence

Let `S ⊆ X` be nonempty, closed and invariant, and fix `ρ : X → S` with `d(x, ρ x) = d(x, S)`.
The relabelling equivalence (`HSP.relabelEquiv hS hρ : HSP.RelabelEquiv G S ρ`) consists of
* `P : 𝒜_𝐆(S) → 𝒜_S`, the pushforward along `S ↪ X`, corestricted;
* `R : 𝒜_S → 𝒜_𝐆(S)`, `R(n_i, x_i) = (n_i, ρ ∘ x_i)`, `R[u] = [u]`;
* `RP = id` on the nose;
* the unit `id ≅ RP`, the identity, and the counit `PR ≅ id`, given by relabelling isomorphisms;
both `P` and `R` are strict duality functors and the unit and counit are unitary.

Lean encoding. `X` is a compact metric space with an isometric `C_p`-action, and the invariant
subset is a `SubAddAction (ZMod p) X`, so that `S` is a metric `C_p`-space (the subtype); it is
compact because it is closed (`hS`). `𝒜_S` is the full subcategory `(supp S).FullSubcategory`,
a duality category since `supp S` is a dual-closed additive subcategory. The map `ρ` is a
parameter with `hρ : ∀ x, dist x (ρ x) = infDist x S`; it exists when `S` is nonempty, and it
need not be equivariant. The functor `R` needs neither that `S` is closed or nonempty nor that `X`
is compact. The triangle identities are not stated.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- A nonempty closed subset of a compact metric space has a nearest-point map
`ρ : X → S`, `d(x, ρ x) = d(x, S)`. -/
private theorem exists_nearest [CompactSpace X] {S : Set X} (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ ρ : X → S, ∀ x, dist x (ρ x : X) = Metric.infDist x S := by
  choose ρ hρS hρ using fun x => hS.isCompact.exists_infDist_eq_dist hne x
  exact ⟨fun x => ⟨ρ x, hρS x⟩, fun x => (hρ x).symm⟩

variable [IsIsometricVAdd (ZMod p) X] (S : SubAddAction (ZMod p) X)

section P

variable [CompactSpace X] {S} (hS : IsClosed (S : Set X))

omit [IsIsometricVAdd (ZMod p) X] in
include hS in
/-- A closed subset of a compact space is compact. -/
private theorem compactSpace_of_isClosed : CompactSpace S :=
  isCompact_iff_compactSpace.1 hS.isCompact

/-- The pushforward along `S ↪ X`. -/
private noncomputable def inclPush : DualFunctor (AsymCat G S) (AsymCat G X) :=
  haveI := compactSpace_of_isClosed hS
  push (G := G) (f := ((↑) : S → X)) continuous_subtype_val fun _ _ => rfl

/-- The underlying functor of `P`: the pushforward along `S ↪ X`, corestricted to `𝒜_S`. -/
private noncomputable def relabelPFunctor :
    AsymCat G S ⥤ (supp (G := G) (S : Set X)).FullSubcategory :=
  ObjectProperty.lift _ (inclPush (G := G) hS).toFunctor
    fun M _ hε => Eventually.of_forall fun i k =>
      Metric.self_subset_thickening hε _ (M.as.x i k).2

private instance : (relabelPFunctor (G := G) hS).Additive where
  map_add := ObjectProperty.hom_ext _ ((inclPush hS).toFunctor.map_add)

private instance : (relabelPFunctor (G := G) hS).Linear ℚ where
  map_smul _ _ := ObjectProperty.hom_ext _ ((inclPush hS).toFunctor.map_smul _ _)

/-- `P : 𝒜_𝐆(S) → 𝒜_S`, `(n_i, x_i) ↦ (n_i, x_i)`, `[u] ↦ [u]`, a duality functor with `ξ = id`. -/
private noncomputable def relabelP :
    DualFunctor (AsymCat G S) (supp (G := G) (S : Set X)).FullSubcategory
    where
  toFunctor := relabelPFunctor hS
  ξ _ := Iso.refl _
  ξ_natural f := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  ξ_dual _ := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]
    exact DualCat.dualHom_id _

omit [IsIsometricVAdd (ZMod p) X] in
/-- `P` is a strict duality functor. -/
private theorem relabelP_isStrict : (relabelP (G := G) hS).IsStrict := fun _ => ⟨rfl, rfl⟩

end P

section R

variable {S} {ρ : X → S} (hρ : ∀ x, dist x (ρ x : X) = Metric.infDist x S)

/-- The relabelled object `(n_i, ρ ∘ x_i)` of `𝒜_𝐆(S)`. -/
private def AsymPre.relabelObj (ρ : X → S) (M : AsymPre G X) : AsymPre G S :=
  ⟨M.n, fun i => ρ ∘ M.x i⟩

omit [IsIsometricVAdd (ZMod p) X] in
include hρ in
/-- For `P ∈ 𝒜_S`, the error `ε_i = max_k d(x_i(k), ρ x_i(k)) = max_k d(x_i(k), S)` tends to
`0`. -/
private theorem tendsto_err {P : AsymCat G X} (hP : supp (S : Set X) P) :
    Tendsto (fun i => Finset.univ.sup fun k => nndist (P.as.x i k) (ρ (P.as.x i k) : X)) atTop
      (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => absurd ha (not_lt.2 zero_le), fun a ha => ?_⟩
  filter_upwards [hP ((a : ℝ) / 2) (by positivity)] with i hi
  refine lt_of_le_of_lt (Finset.sup_le fun k _ => ?_) (NNReal.half_lt_self ha.ne')
  obtain ⟨s, hs, hd⟩ := Metric.mem_thickening_iff.1 (hi k)
  rw [← NNReal.coe_le_coe, coe_nndist, NNReal.coe_div, NNReal.coe_two, hρ]
  exact ((Metric.infDist_le_dist_of_mem hs).trans_lt hd).le

omit [IsIsometricVAdd (ZMod p) X] in
/-- Propagation in `S` is propagation in `X`. -/
private theorem prop_val {B B' : Type*} [Fintype B] [Fintype B'] (l : B → S) (l' : B' → S)
    (u : Matrix B' B ℚ) : prop l l' u = prop (Subtype.val ∘ l) (Subtype.val ∘ l') u := rfl

/-- `R[u] = [u]` on sequences: the matrices are unchanged, with propagation at most
`prop(u_i) + ε_i(P) + ε_i(Q)`. -/
private def relabelHom {P Q : AsymCat G X} (hP : supp (S : Set X) P) (hQ : supp (S : Set X) Q)
    (u : P.as ⟶ Q.as) : AsymPre.relabelObj ρ P.as ⟶ AsymPre.relabelObj ρ Q.as :=
  AsymPre.homMk (fun i => AsymPre.coord u i) (by
    have h := ((AsymPre.tendsto_prop u).add (tendsto_err hρ hP)).add (tendsto_err hρ hQ)
    rw [add_zero, add_zero] at h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le) fun i => ?_
    refine (prop_val _ _ _).trans_le ((prop_relabel_le (P.as.label i)
      (Subtype.val ∘ (AsymPre.relabelObj ρ P.as).label i) (Q.as.label i)
      (Subtype.val ∘ (AsymPre.relabelObj ρ Q.as).label i) _).trans ?_)
    refine add_le_add (add_le_add le_rfl (Finset.sup_le fun b _ => ?_))
      (Finset.sup_le fun b _ => ?_)
    · simp only [Function.comp, AsymPre.label, AsymPre.relabelObj, SubAddAction.val_vadd,
        nndist_vadd]
      exact Finset.le_sup (f := fun k => nndist (P.as.x i k) (ρ (P.as.x i k) : X))
        (Finset.mem_univ b.2)
    · simp only [Function.comp, AsymPre.label, AsymPre.relabelObj, SubAddAction.val_vadd,
        nndist_vadd]
      exact Finset.le_sup (f := fun k => nndist (Q.as.x i k) (ρ (Q.as.x i k) : X))
        (Finset.mem_univ b.2))

/-- `R` on morphisms of `𝒜_S`: `[u] ↦ [u]`. -/
private def relabelMap {P Q : AsymCat G X} (hP : supp (S : Set X) P) (hQ : supp (S : Set X) Q)
    (f : P ⟶ Q) : (⟨AsymPre.relabelObj ρ P.as⟩ : AsymCat G S) ⟶ ⟨AsymPre.relabelObj ρ Q.as⟩ :=
  Quot.lift (fun u => AsymCat.mkHom (relabelHom hρ hP hQ u)) (fun a b h => by
    rw [HomRel.compClosure_iff_self] at h
    exact (AsymCat.mkHom_eq_iff _ _).2 h) f

private theorem relabelMap_mkHom {M N : AsymPre G X} (hM : supp (S : Set X) ⟨M⟩)
    (hN : supp (S : Set X) ⟨N⟩) (u : M ⟶ N) :
    relabelMap hρ hM hN (AsymCat.mkHom u) = AsymCat.mkHom (relabelHom hρ hM hN u) := rfl

/-- The underlying functor of `R : 𝒜_S → 𝒜_𝐆(S)`. -/
private def relabelRFunctor : (supp (G := G) (S : Set X)).FullSubcategory ⥤ AsymCat G S where
  obj V := ⟨AsymPre.relabelObj ρ V.obj.as⟩
  map {V W} f := relabelMap hρ V.property W.property f.hom
  map_id V := congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => rfl)
  map_comp {U V W} f g := by
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective f.hom
    obtain ⟨v, hv⟩ := AsymCat.mkHom_surjective g.hom
    show relabelMap hρ _ _ (f.hom ≫ g.hom) = relabelMap hρ _ _ f.hom ≫ relabelMap hρ _ _ g.hom
    rw [← hu, ← hv, ← Functor.map_comp, relabelMap_mkHom, relabelMap_mkHom, relabelMap_mkHom,
      ← Functor.map_comp]
    exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => rfl)

private instance : (relabelRFunctor (G := G) hρ).Additive where
  map_add {V W f g} := by
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective f.hom
    obtain ⟨v, hv⟩ := AsymCat.mkHom_surjective g.hom
    show relabelMap hρ _ _ (f.hom + g.hom) = relabelMap hρ _ _ f.hom + relabelMap hρ _ _ g.hom
    rw [← hu, ← hv, ← Functor.map_add, relabelMap_mkHom, relabelMap_mkHom, relabelMap_mkHom,
      ← Functor.map_add]
    exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => rfl)

private instance : (relabelRFunctor (G := G) hρ).Linear ℚ where
  map_smul {V W} f c := by
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective f.hom
    show relabelMap hρ _ _ (c • f.hom) = c • relabelMap hρ _ _ f.hom
    rw [← hu, ← Functor.map_smul, relabelMap_mkHom, relabelMap_mkHom, ← Functor.map_smul]
    exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => rfl)

/-- `R : 𝒜_S → 𝒜_𝐆(S)`, `(n_i, x_i) ↦ (n_i, ρ ∘ x_i)`, `[u] ↦ [u]`, a duality functor with
`ξ = id`. -/
private def relabelR : DualFunctor (supp (G := G) (S : Set X)).FullSubcategory (AsymCat G S) where
  toFunctor := relabelRFunctor hρ
  ξ _ := Iso.refl _
  ξ_natural {V W} f := by
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective f.hom
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    show relabelMap hρ _ _ (DualCat.dualHom f.hom) = DualCat.dualHom (relabelMap hρ _ _ f.hom)
    rw [← hu, AsymCat.dualHom_mkHom, relabelMap_mkHom, relabelMap_mkHom, AsymCat.dualHom_mkHom]
    exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun _ => rfl)
  ξ_dual _ := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]
    exact DualCat.dualHom_id _

/-- `R` is a strict duality functor. -/
private theorem relabelR_isStrict : (relabelR (G := G) hρ).IsStrict := fun _ => ⟨rfl, rfl⟩

end R

section Equivalence

variable [CompactSpace X] {S} (hS : IsClosed (S : Set X)) {ρ : X → S}
  (hρ : ∀ x, dist x (ρ x : X) = Metric.infDist x S)

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
include hρ in
/-- `ρ` fixes `S` pointwise. -/
private theorem rho_val (s : S) : ρ s = s := by
  refine Subtype.ext (dist_eq_zero.1 ?_).symm
  rw [hρ]
  exact Metric.infDist_zero_of_mem s.2

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
/-- Morphisms with the same matrices between equal objects agree up to the transports. -/
private theorem mkHom_eq_eqToHom {M M' N N' : AsymPre G S} (hM : M' = M) (hN : N' = N)
    (u : M ⟶ N) (u' : M' ⟶ N') (h : ∀ i, HEq (AsymPre.coord u' i) (AsymPre.coord u i)) :
    AsymCat.mkHom u' = eqToHom (congrArg (fun M => (⟨M⟩ : AsymCat G S)) hM) ≫ AsymCat.mkHom u ≫
      eqToHom (congrArg (fun M => (⟨M⟩ : AsymCat G S)) hN.symm) := by
  subst hM hN
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg AsymCat.mkHom (AsymPre.hom_ext fun i => eq_of_heq (h i))

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
include hρ in
private theorem relabelObj_pushObj (M : AsymPre G S) :
    AsymPre.relabelObj ρ ⟨M.n, fun i => Subtype.val ∘ M.x i⟩ = M := by
  obtain ⟨n, x⟩ := M
  simp only [AsymPre.relabelObj, AsymPre.mk.injEq, heq_eq_eq, true_and]
  exact funext fun i => funext fun k => rho_val hρ (x i k)

/-- `RP = id` on the nose. -/
private theorem relabelP_comp_relabelR :
    (relabelP (G := G) hS).toFunctor ⋙ (relabelR hρ).toFunctor = 𝟭 _ :=
  CategoryTheory.Functor.ext
    (fun M => congrArg (fun M => (⟨M⟩ : AsymCat G S)) (relabelObj_pushObj hρ M.as)) fun M N f => by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    exact mkHom_eq_eqToHom (relabelObj_pushObj hρ M.as) (relabelObj_pushObj hρ N.as) u _
      fun _ => HEq.rfl

/-- The unit `id ≅ RP`, the identity, is unitary. -/
private noncomputable def relabelUnit :
    DualFunctor.UnitaryIso (DualFunctor.id (AsymCat G S)) ((relabelP hS).comp (relabelR hρ)) where
  iso := eqToIso (show (DualFunctor.id _).toFunctor = ((relabelP hS).comp (relabelR hρ)).toFunctor
    from (relabelP_comp_relabelR hS hρ).symm)
  unitary M := by
    rw [eqToIso.hom, eqToHom_app, eqToHom_app, DualCat.dualHom_eqToHom]
    simp only [DualFunctor.comp_ξ, DualFunctor.id_ξ, relabelP, relabelR, Iso.trans_hom,
      Functor.mapIso_hom, Iso.refl_hom]
    erw [Category.id_comp, Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl

omit [IsIsometricVAdd (ZMod p) X] [CompactSpace X] in
include hρ in
/-- `ε_i(M) → 0` for the counit: `max_k d(ρ x_i(k), x_i(k)) → 0` for `M ∈ 𝒜_S`. -/
private theorem tendsto_counit (V : (supp (G := G) (S : Set X)).FullSubcategory) :
    Tendsto (fun i => Finset.univ.sup fun k =>
      nndist (ρ (V.obj.as.x i k) : X) (V.obj.as.x i k)) atTop (𝓝 0) := by
  simpa only [nndist_comm] using tendsto_err hρ V.property

/-- The component `PR(M) ≅ M` of the counit, the relabelling isomorphism. -/
private noncomputable def relabelCounitApp (V : (supp (G := G) (S : Set X)).FullSubcategory) :
    (relabelP hS).toFunctor.obj ((relabelR hρ).toFunctor.obj V) ≅ V :=
  ObjectProperty.isoMk _ (relabelIso (n := V.obj.as.n) (x := fun i k => (ρ (V.obj.as.x i k) : X))
    (x' := V.obj.as.x) (tendsto_counit hρ V))

/-- The counit `PR ≅ id`, given by relabelling isomorphisms, is a unitary natural isomorphism. -/
private noncomputable def relabelCounit :
    DualFunctor.UnitaryIso ((relabelR hρ).comp (relabelP hS))
      (DualFunctor.id (supp (G := G) (S : Set X)).FullSubcategory) where
  iso := NatIso.ofComponents (relabelCounitApp hS hρ) fun {V W} f => by
    apply ObjectProperty.hom_ext
    obtain ⟨u, hu⟩ := AsymCat.mkHom_surjective f.hom
    show ((relabelPFunctor hS).map (relabelMap hρ V.property W.property f.hom)).hom ≫
      (relabelIso (tendsto_counit hρ W)).hom = (relabelIso (tendsto_counit hρ V)).hom ≫ f.hom
    rw [← hu, relabelMap_mkHom]
    exact relabelIso_natural _ _ _ u fun _ => rfl
  unitary V := by
    apply ObjectProperty.hom_ext
    show (relabelIso (tendsto_counit hρ V)).hom ≫ 𝟙 _ ≫
      DualCat.dualHom (relabelIso (tendsto_counit hρ V)).hom = _
    rw [relabelIso_dual, Category.id_comp, Iso.hom_inv_id]
    simp [relabelP, relabelR]
    rfl

/-- The data of the relabelling equivalence for `S` and `ρ`: the functors `P : 𝒜_𝐆(S) → 𝒜_S`
(the pushforward along `S ↪ X`, corestricted) and `R : 𝒜_S → 𝒜_𝐆(S)` with
`R(n_i, x_i) = (n_i, ρ ∘ x_i)`, both strict duality functors, with `RP = id` on the nose, the
unit `id ≅ RP` and the counit `PR ≅ id` unitary natural isomorphisms. -/
structure RelabelEquiv (G : GroupSeq p) (S : SubAddAction (ZMod p) X) (ρ : X → S) where
  /-- `P : 𝒜_𝐆(S) → 𝒜_S`. -/
  P : DualFunctor (AsymCat G S) (supp (G := G) (S : Set X)).FullSubcategory
  /-- `R : 𝒜_S → 𝒜_𝐆(S)`. -/
  R : DualFunctor (supp (G := G) (S : Set X)).FullSubcategory (AsymCat G S)
  /-- `P` is the pushforward along `S ↪ X` on objects. -/
  P_obj : ∀ M, (P.toFunctor.obj M).obj = ⟨⟨M.as.n, fun i => Subtype.val ∘ M.as.x i⟩⟩
  /-- `R(n_i, x_i) = (n_i, ρ ∘ x_i)`. -/
  R_obj : ∀ V, R.toFunctor.obj V = ⟨⟨V.obj.as.n, fun i => ρ ∘ V.obj.as.x i⟩⟩
  /-- `P` is strict. -/
  P_isStrict : P.IsStrict
  /-- `R` is strict. -/
  R_isStrict : R.IsStrict
  /-- `RP = id` on the nose. -/
  comp_eq : P.toFunctor ⋙ R.toFunctor = 𝟭 _
  /-- The unit `id ≅ RP`, unitary. -/
  unit : DualFunctor.UnitaryIso (DualFunctor.id _) (P.comp R)
  /-- The counit `PR ≅ id`, unitary. -/
  counit : DualFunctor.UnitaryIso (R.comp P) (DualFunctor.id _)

/-- **The relabelling equivalence** for a closed invariant `S` and `ρ` with
`d(x, ρ x) = d(x, S)`. -/
noncomputable def relabelEquiv : RelabelEquiv G S ρ where
  P := relabelP hS
  R := relabelR hρ
  P_obj _ := rfl
  R_obj _ := rfl
  P_isStrict := relabelP_isStrict hS
  R_isStrict := relabelR_isStrict hρ
  comp_eq := relabelP_comp_relabelR hS hρ
  unit := relabelUnit hS hρ
  counit := relabelCounit hS hρ

end Equivalence

end HSP

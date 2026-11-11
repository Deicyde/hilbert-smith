import HilbertSmithPaper.LTheory.Base.Pairs.PoincarePair
import HilbertSmithPaper.LTheory.Base.Complexes.StructurePushInvolution
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.DualMapIso
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushComp
import HilbertSmithPaper.LTheory.Base.Complexes.Functors.PushId

/-!
# Transport of pairs along isomorphisms

If `(f : C ⟶ D, δφ, φ)` is a strict `n`-dimensional Poincaré pair, `u : C' ≅ C` an isomorphism
of complexes, `φ' ∈ M(C')_m` with `u_% φ' = φ`, and `s ∈ {1, -1}` (a unit of `ℤ`), then
`(f ∘ u, s δφ, s φ')` is a strict `n`-dimensional Poincaré pair.

Proof: `φ' = (u⁻¹)_% φ` is a `T`-invariant cycle with `φ'_♮ = u⁻¹ ∘ φ_♮ ∘ (u⁻¹)^{m-*}`; the
isomorphism `κ : 𝒞(f u) ≅ 𝒞(f)`, `(x, y) ↦ (x, u y)`, carries the new pair map to `s ψ`; and
multiplying a chain homotopy equivalence and its inverse by `s` gives one.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

open DualCat

universe v u

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℚ B] [HasFiniteBiproducts B]
  [DualCat B]

namespace PairTransport

private lemma units_smul_apply {M N : ModuleCat.{v} ℚ} (g : M ⟶ N) (s : ℤˣ) (x : M) :
    g (s • x) = s • g x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private lemma push_inv_hom {C C' : ChainComplex B ℤ} (u : C' ≅ C) (n : ℤ)
    (x : (StructureCx C').X n) :
    (StructureCx.push u.inv).f n ((StructureCx.push u.hom).f n x) = x := by
  have := ConcreteCategory.congr_hom
    (congrArg (fun h => h.f n) (StructureCx.push_comp u.hom u.inv)) x
  simp only [u.hom_inv_id, StructureCx.push_id] at this
  simpa using this.symm

/-- Multiplying a chain homotopy equivalence and its inverse by a unit `s` of `ℤ`. -/
private def unitSmul {C D : ChainComplex B ℤ} (s : ℤˣ) (e : HomotopyEquiv C D) :
    HomotopyEquiv C D where
  hom := s • e.hom
  inv := s • e.inv
  homotopyHomInvId := (Homotopy.ofEq (by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
      one_smul])).trans e.homotopyHomInvId
  homotopyInvHomId := (Homotopy.ofEq (by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
      one_smul])).trans e.homotopyInvHomId

/-- The isomorphism `𝒞(u ≫ f) ≅ 𝒞(f)`, `(x, y) ↦ (x, u y)`, for an isomorphism `u`. -/
private noncomputable def coneIso {C C' D : ChainComplex B ℤ} (u : C' ≅ C) (f : C ⟶ D) :
    cone (u.hom ≫ f) ≅ cone f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => biprod.mapIso (Iso.refl (D.X r)) ((HomologicalComplex.eval _ _ (r - 1)).mapIso u))
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      obtain rfl : j = i - 1 := by omega
      change _ ≫ cone.d _ i (i - 1) = cone.d _ i (i - 1) ≫ _
      simp only [cone.d, dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        Category.comp_id]
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp)

omit [Linear ℚ B] [DualCat B] in
private lemma coneIso_hom_f {C C' D : ChainComplex B ℤ} (u : C' ≅ C) (f : C ⟶ D) (r : ℤ) :
    (coneIso u f).hom.f r = biprod.map (𝟙 (D.X r)) (u.hom.f (r - 1)) := rfl

end PairTransport

open PairTransport in
/-- Transport of a pair along an isomorphism `u : C' ≅ C` of its boundary complex carrying
`φ'` to `φ`, combined with the sign `s ∈ {1, -1}`. -/
theorem SymPair.transport {m n : ℤ} (W : SymPair B m n) {C' : ChainComplex B ℤ} (u : C' ≅ W.C)
    (φ' : (StructureCx C').X m) (hφ' : (StructureCx.push u.hom).f m φ' = W.φ) (s : ℤˣ) :
    ∃ W' : SymPair B m n, W'.data = ⟨C', W.D, u.hom ≫ W.f, s • W.δφ, s • φ'⟩ := by
  have hφ'eq : φ' = (StructureCx.push u.inv).f m W.φ := by
    rw [← hφ', push_inv_hom]
  have hcyc' : (StructureCx C').d m (m - 1) φ' = 0 := by
    rw [hφ'eq, StructureCx.d_push_apply, W.boundary_cycle, map_zero]
  have hcyc : (StructureCx C').d m (m - 1) (s • φ') = 0 := by
    rw [units_smul_apply, hcyc', smul_zero]
  have hrel : (StructureCx W.D).d n m (s • W.δφ) =
      (StructureCx.push (u.hom ≫ W.f)).f m (s • φ') := by
    rw [units_smul_apply, units_smul_apply, W.rel, ← hφ', StructureCx.push_comp]
    rfl
  refine ⟨
    { C := C'
      D := W.D
      f := u.hom ≫ W.f
      δφ := s • W.δφ
      φ := s • φ'
      dim := W.dim
      boundary_bounded := fun r hr => IsZero.of_iso (W.boundary_bounded r hr)
        ((HomologicalComplex.eval _ _ r).mapIso u)
      boundary_cycle := hcyc
      boundary_symmetric := by
        rw [units_smul_apply, hφ'eq, StructureCx.T_push_apply, W.boundary_symmetric]
      boundary_poincare := ?_
      bounded := W.bounded
      symmetric := by rw [units_smul_apply, W.symmetric]
      rel := hrel
      poincare := ?_ }, rfl⟩
  · obtain ⟨e, he⟩ := W.boundary_poincare
    refine ⟨unitSmul s ((HomotopyEquiv.ofIso (dualCx.mapIso u m).symm).trans
      (e.trans (HomotopyEquiv.ofIso u.symm))), ?_⟩
    ext r
    change s • (dualHom (u.inv.f (m - r)) ≫ e.hom.f r ≫ u.inv.f r) = (s • φ') ⟨(r, m - r), _⟩
    rw [he, hφ'eq]
    rfl
  · obtain ⟨e, he⟩ := W.poincare
    refine ⟨(unitSmul s e).trans (HomotopyEquiv.ofIso (coneIso u W.f).symm), ?_⟩
    change (s • e.hom) ≫ (coneIso u W.f).inv = _
    rw [he, Iso.comp_inv_eq]
    refine HomologicalComplex.hom_ext _ _ fun r => ?_
    rw [HomologicalComplex.comp_f, coneIso_hom_f]
    apply biprod.hom_ext
    · simp [pairMap]
    · have key : dualHom (u.hom.f (n - r)) ≫ dualHom (u.inv.f (n - r)) = 𝟙 _ := by
        rw [← dualHom_comp, ← HomologicalComplex.comp_f, u.inv_hom_id, HomologicalComplex.id_f,
          dualHom_id]
      have key2 : u.inv.f (r - 1) ≫ u.hom.f (r - 1) = 𝟙 _ := by
        rw [← HomologicalComplex.comp_f, u.inv_hom_id, HomologicalComplex.id_f]
      have hpush : ∀ (p q : ℤ) (h : p + q = m), ((StructureCx.push u.inv).f m W.φ) ⟨(p, q), h⟩ =
          dualHom (u.inv.f q) ≫ W.φ ⟨(p, q), h⟩ ≫ u.inv.f p := fun _ _ _ => rfl
      simp [pairMap, hφ'eq, hpush, reassoc_of% key, key2, smul_comm s]

end HSP

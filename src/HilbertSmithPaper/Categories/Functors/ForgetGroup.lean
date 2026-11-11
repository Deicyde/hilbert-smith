import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.AsymptoticDuality
import HilbertSmithPaper.LTheory.Base.Categories.DualityFunctor

/-!
# Forgetting the group

For a finite group `G` the bijection `ε_G : G → {0..|G|-1}` is `Fintype.equivFin G`, fixed once,
and the *group enumeration* is `e^G_n : G × Fin n ≃ Fin (|G| n)`, `e(g, k) = ε_G(g) n + k`
(`HSP.groupEnum`). `U : 𝒜_𝐆(X) → 𝒜_𝟏(X)` sends `(n_i, x_i)` to
`(|G_i| n_i, λ_i ∘ (e^{G_i}_{n_i})⁻¹)` and `[u]` to `[ū]`, with `ū_i` the matrix `u_i` with rows
and columns reindexed along `e^{G_i}`.

Lean encoding. In `𝒜_𝟏(X)` the basis at level `i` is `Unit × Fin (|G_i| n_i)` (the trivial group
times the enumeration), so the reindexing is along
`Unit × Fin (|G_i| n_i) ≃ Fin (|G_i| n_i) ≃ G_i × Fin n_i`. Reindexing along a bijection preserves
identity matrices, products and transposes, and keeps every entry beside the same pair of labels,
so the propagation does not grow. `HSP.forgetGroup` is the duality functor, with `ξ = id`; it is
strict (`HSP.forgetGroup_isStrict`).
-/

open CategoryTheory CategoryTheory.Limits Filter

namespace HSP

/-- The group enumeration `e^G_n : G × Fin n ≃ Fin (|G| n)`, `e(g, k) = ε_G(g) n + k` with
`ε_G = Fintype.equivFin G`. -/
noncomputable def groupEnum (G : Type*) [Fintype G] (n : ℕ) : G × Fin n ≃ Fin (Fintype.card G * n) :=
  ((Fintype.equivFin G).prodCongr (Equiv.refl _)).trans finProdFinEquiv

variable {p : ℕ} {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- Reindexing does not increase propagation. -/
private theorem prop_submatrix_le {B B' C C' : Type*} [Fintype B] [Fintype B'] [Fintype C]
    [Fintype C'] (l : B → X) (l' : B' → X) (u : Matrix B' B ℚ) (e : C → B) (e' : C' → B') :
    prop (l ∘ e) (l' ∘ e') (u.submatrix e' e) ≤ prop l l' u :=
  Finset.sup_le fun q hq =>
    Finset.le_sup (f := fun q : B' × B => nndist (l' q.1) (l q.2)) (b := (e' q.1, e q.2))
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hq).2⟩)

namespace AsymPre

/-- The reindexing `Unit × Fin (|G_i| n) ≃ G_i × Fin n` of forgetting the group. -/
noncomputable def forgetEquiv (G : GroupSeq p) (i n : ℕ) :
    (GroupSeq.trivial p).G i × Fin (Fintype.card (G.G i) * n) ≃ G.G i × Fin n :=
  (Equiv.uniqueProd _ _).trans (groupEnum (G.G i) n).symm

/-- The object `(|G_i| n_i, λ_i ∘ (e^{G_i}_{n_i})⁻¹)` of `𝒜_𝟏(X)`. -/
noncomputable def forgetObj (M : AsymPre G X) : AsymPre (GroupSeq.trivial p) X where
  n i := Fintype.card (G.G i) * M.n i
  x i j := M.label i ((groupEnum (G.G i) (M.n i)).symm j)

omit [MetricSpace X] in
theorem label_forgetObj (M : AsymPre G X) (i : ℕ) :
    (forgetObj M).label i = M.label i ∘ forgetEquiv G i (M.n i) := by
  funext b
  show (GroupSeq.trivial p).χ i b.1 +ᵥ M.label i ((groupEnum (G.G i) (M.n i)).symm b.2) =
    M.label i ((groupEnum (G.G i) (M.n i)).symm b.2)
  exact zero_vadd _ _

/-- The reindexed matrix `ū_i`. -/
noncomputable def forgetMat {M N : AsymPre G X} (u : M ⟶ N) (i : ℕ) :
    (forgetObj M).free i ⟶ (forgetObj N).free i :=
  FreeCat.ofMat ((FreeCat.mat (coord u i)).submatrix (forgetEquiv G i (N.n i))
    (forgetEquiv G i (M.n i))) (fun _ _ _ _ _ => rfl)

/-- Forgetting the group on sequences. -/
@[simps]
noncomputable def forget : AsymPre G X ⥤ AsymPre (GroupSeq.trivial p) X where
  obj M := forgetObj M
  map {M N} u := homMk (forgetMat u) (by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_prop u)
      (fun _ => zero_le) fun i => ?_
    show prop ((forgetObj M).label i) ((forgetObj N).label i) _ ≤ _
    rw [label_forgetObj, label_forgetObj]
    exact prop_submatrix_le _ _ _ _ _)
  map_id M := hom_ext fun i => FreeCat.hom_ext (Matrix.submatrix_one_equiv _)
  map_comp u v := hom_ext fun i => FreeCat.hom_ext
    (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

end AsymPre

/-- The underlying functor of forgetting the group, `𝒜_𝐆(X) ⥤ 𝒜_𝟏(X)`. -/
noncomputable def forgetGroupFunctor : AsymCat G X ⥤ AsymCat (GroupSeq.trivial p) X :=
  CategoryTheory.Quotient.lift (asymRel G X)
    (AsymPre.forget ⋙ Quotient.functor (asymRel (GroupSeq.trivial p) X)) fun _ _ _ _ h =>
      CategoryTheory.Quotient.sound _ (h.mono fun i h => by
        show AsymPre.forgetMat _ i = AsymPre.forgetMat _ i
        simp only [AsymPre.forgetMat, h])

instance : (forgetGroupFunctor (G := G) (X := X)).Additive where
  map_add {P Q f g} := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    obtain ⟨v, rfl⟩ := AsymCat.mkHom_surjective g
    rw [← (Quotient.functor (asymRel G X)).map_add]
    rfl

instance : (forgetGroupFunctor (G := G) (X := X)).Linear ℚ where
  map_smul {P Q} f c := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    rw [← (Quotient.functor (asymRel G X)).map_smul]
    rfl

/-- Forgetting the group, `U : 𝒜_𝐆(X) → 𝒜_𝟏(X)`, a duality functor with `ξ = id`. -/
noncomputable def forgetGroup : DualFunctor (AsymCat G X) (AsymCat (GroupSeq.trivial p) X) where
  toFunctor := forgetGroupFunctor
  ξ _ := Iso.refl _
  ξ_natural f := by
    obtain ⟨u, rfl⟩ := AsymCat.mkHom_surjective f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  ξ_dual _ := by
    simp only [Iso.refl_hom, eqToHom_refl, Category.comp_id]
    exact DualCat.dualHom_id _

/-- Forgetting the group is a strict duality functor. -/
theorem forgetGroup_isStrict : (forgetGroup (G := G) (X := X)).IsStrict := fun _ => ⟨rfl, rfl⟩

end HSP

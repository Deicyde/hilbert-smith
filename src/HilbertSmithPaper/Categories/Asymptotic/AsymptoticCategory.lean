import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.GroupSequence
import HilbertSmithPaper.Categories.Asymptotic.Propagation
import HilbertSmithPaper.Categories.Asymptotic.PropAdd
import HilbertSmithPaper.Categories.Asymptotic.PropSmul
import HilbertSmithPaper.Categories.Asymptotic.PropMul
import HilbertSmithPaper.Categories.Asymptotic.PropOne
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory

/-!
# Asymptotic category

Let `X` be a metric space with a `C_p`-action and `𝐆` a group sequence. An object of `𝒜_𝐆(X)` is
a sequence `(n_i, x_i)` with `n_i ∈ ℕ` and `x_i : Fin n_i → X`. Its basis at `i` is the free
`G_i`-set `B_i = G_i × Fin n_i`, with labels `λ_i (g, k) = χ_i(g) +ᵥ x_i(k)`. A morphism is a
sequence of `G_i`-equivariant matrices `u_i ∈ ℚ^{B'_i × B_i}` with `prop(u_i) → 0`, taken modulo
eventual equality. The category is `ℚ`-linear and additive, the sum given by concatenating the
`x_i`.

Lean encoding (designed for the support subcategories, the support filtrations and their
quotients, the exterior quotient, and the functors forgetting the group, the control space or the
labels).
* `HSP.AsymPre G X` is the structure of objects `(n, x)` (with the group sequence as a parameter,
  so that the category structures below are attached to it). Its level-`i` object of
  `Free(ℚ[G_i])` is `M.free i = ⟨n_i⟩`, so each `u_i` is a morphism `M.free i ⟶ N.free i` of
  `HSP.FreeCat (G.G i)` (an equivariant matrix), and the labels are `M.label i`.
* `AsymPre G X` is first made a category whose morphisms are the sequences `u` with
  `prop(u_i) → 0` (`HSP.AsymPre.preHom`, a `ℚ`-submodule of the sequences of equivariant
  matrices); composition is levelwise matrix product. It is preadditive and `ℚ`-linear.
* `HSP.AsymCat G X` is Mathlib's quotient category `CategoryTheory.Quotient` of `AsymPre G X` by
  eventual equality `HSP.asymRel` (a congruence compatible with sums and scalars), with
  Mathlib's induced preadditive and `ℚ`-linear structures. Its objects are `⟨M⟩` for
  `M : AsymPre G X`; `HSP.AsymCat.mkHom u` is the class `[u]`.
* The binary biproduct of `⟨M⟩` and `⟨N⟩` is the concatenation `M.sum N`
  (`n_i + m_i`, `Fin.append`), with the coordinate inclusions and projections of
  `Free(ℚ[G_i])` at each level (propagation `0`); the zero object is the empty sequence.
  Hence `𝒜_𝐆(X)` has finite biproducts.
* Neither compactness of `X` nor isometry of the action is needed for these structures.
-/

open CategoryTheory CategoryTheory.Limits Filter Topology
open scoped NNReal

namespace HSP

variable {p : ℕ}

/-- An object `(n_i, x_i)` of the asymptotic category `𝒜_𝐆(X)`: ranks `n_i ∈ ℕ` and labels
`x_i : Fin n_i → X`. The group sequence `G` is a parameter of the type, not of the data. -/
structure AsymPre (G : GroupSeq p) (X : Type*) where
  /-- The rank `n_i` at level `i`. -/
  n : ℕ → ℕ
  /-- The labels `x_i : Fin n_i → X`. -/
  x : ∀ i, Fin (n i) → X

namespace AsymPre

variable {G : GroupSeq p} {X : Type*} [MetricSpace X] [AddAction (ZMod p) X]

/-- The object `n_i` of `Free(ℚ[G_i])`, with basis `G_i × Fin n_i`. -/
def free (M : AsymPre G X) (i : ℕ) : FreeCat (G.G i) := ⟨M.n i⟩

/-- The labels `λ_i (g, k) = χ_i(g) +ᵥ x_i(k)` of the basis `G_i × Fin n_i`. -/
def label (M : AsymPre G X) (i : ℕ) : G.G i × Fin (M.n i) → X :=
  fun b => G.χ i b.1 +ᵥ M.x i b.2

/-- The sequences of equivariant matrices `u_i : M_i → N_i` with `prop(u_i) → 0`. -/
def preHom (M N : AsymPre G X) : Submodule ℚ (∀ i, M.free i ⟶ N.free i) where
  carrier := {u | Tendsto (fun i => prop (M.label i) (N.label i) (FreeCat.mat (u i))) atTop (𝓝 0)}
  add_mem' {u v} hu hv := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hu.max hv) (fun _ => zero_le) fun i => ?_
    exact prop_add_le (M.label i) (N.label i) (FreeCat.mat (u i)) (FreeCat.mat (v i))
  zero_mem' := by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    exact prop_zero _ _
  smul_mem' c u hu := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => zero_le) fun i => ?_
    exact prop_smul_le (M.label i) (N.label i) c (FreeCat.mat (u i))

instance : Quiver (AsymPre G X) where
  Hom M N := preHom M N

/-- The level-`i` matrix `u_i` of a morphism. -/
def coord {M N : AsymPre G X} (u : M ⟶ N) (i : ℕ) : M.free i ⟶ N.free i :=
  Subtype.val (p := fun u => u ∈ preHom M N) u i

theorem tendsto_prop {M N : AsymPre G X} (u : M ⟶ N) :
    Tendsto (fun i => prop (M.label i) (N.label i) (FreeCat.mat (coord u i))) atTop (𝓝 0) :=
  u.2

@[ext]
theorem hom_ext {M N : AsymPre G X} {u v : M ⟶ N} (h : ∀ i, coord u i = coord v i) : u = v :=
  Subtype.ext (funext h)

/-- A morphism from a sequence of equivariant matrices with propagation tending to `0`. -/
def homMk {M N : AsymPre G X} (u : ∀ i, M.free i ⟶ N.free i)
    (hu : Tendsto (fun i => prop (M.label i) (N.label i) (FreeCat.mat (u i))) atTop (𝓝 0)) :
    M ⟶ N := ⟨u, hu⟩

@[simp] theorem coord_homMk {M N : AsymPre G X} (u : ∀ i, M.free i ⟶ N.free i) (hu) (i : ℕ) :
    coord (homMk u hu) i = u i := rfl

instance : Category (AsymPre G X) where
  id M := homMk (fun i => 𝟙 (M.free i)) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    exact prop_one _)
  comp u v := homMk (fun i => coord u i ≫ coord v i) (by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (tendsto_prop v).add (tendsto_prop u)) (fun _ => zero_le) fun i => ?_
    exact prop_mul_le _ _ _ (FreeCat.mat (coord u i)) (FreeCat.mat (coord v i)))
  id_comp _ := hom_ext fun _ => Category.id_comp _
  comp_id _ := hom_ext fun _ => Category.comp_id _
  assoc _ _ _ := hom_ext fun _ => Category.assoc _ _ _

@[simp] theorem coord_id (M : AsymPre G X) (i : ℕ) : coord (𝟙 M) i = 𝟙 (M.free i) := rfl
@[simp] theorem coord_comp {M N P : AsymPre G X} (u : M ⟶ N) (v : N ⟶ P) (i : ℕ) :
    coord (u ≫ v) i = coord u i ≫ coord v i := rfl

instance (M N : AsymPre G X) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs (AddCommGroup (preHom M N))

instance (M N : AsymPre G X) : Module ℚ (M ⟶ N) :=
  inferInstanceAs (Module ℚ (preHom M N))

@[simp] theorem coord_add {M N : AsymPre G X} (u v : M ⟶ N) (i : ℕ) :
    coord (u + v) i = coord u i + coord v i := rfl
@[simp] theorem coord_zero {M N : AsymPre G X} (i : ℕ) : coord (0 : M ⟶ N) i = 0 := rfl
@[simp] theorem coord_neg {M N : AsymPre G X} (u : M ⟶ N) (i : ℕ) :
    coord (-u) i = -coord u i := rfl
@[simp] theorem coord_sub {M N : AsymPre G X} (u v : M ⟶ N) (i : ℕ) :
    coord (u - v) i = coord u i - coord v i := rfl
@[simp] theorem coord_smul {M N : AsymPre G X} (c : ℚ) (u : M ⟶ N) (i : ℕ) :
    coord (c • u) i = c • coord u i := rfl

instance : Preadditive (AsymPre G X) where
  add_comp _ _ _ f f' g := hom_ext fun i => by
    simp only [coord_comp, coord_add, Preadditive.add_comp]
  comp_add _ _ _ f g g' := hom_ext fun i => by
    simp only [coord_comp, coord_add, Preadditive.comp_add]

instance : Linear ℚ (AsymPre G X) where
  smul_comp _ _ _ c f g := hom_ext fun i => by
    simp only [coord_comp, coord_smul, Linear.smul_comp]
  comp_smul _ _ _ f c g := hom_ext fun i => by
    simp only [coord_comp, coord_smul, Linear.comp_smul]

/-- A matrix all of whose nonzero entries join equal labels has propagation `0`. -/
private theorem prop_eq_zero_of {B B' : Type*} [Fintype B] [Fintype B'] (l : B → X)
    (l' : B' → X) (u : Matrix B' B ℚ) (h : ∀ b' b, u b' b ≠ 0 → l' b' = l b) :
    prop l l' u = 0 :=
  le_antisymm (Finset.sup_le fun q hq => by
    rw [h q.1 q.2 (Finset.mem_filter.1 hq).2, nndist_self]) zero_le

/-- The concatenation `(n_i + m_i, x_i ⧺ y_i)`. -/
def sum (M N : AsymPre G X) : AsymPre G X where
  n i := M.n i + N.n i
  x i := Fin.append (M.x i) (N.x i)

omit [MetricSpace X] in
private theorem label_sum_castAdd (M N : AsymPre G X) (i : ℕ) (g : G.G i) (k : Fin (M.n i)) :
    (M.sum N).label i (g, Fin.castAdd (N.n i) k) = M.label i (g, k) := by
  simp [label, sum]

omit [MetricSpace X] in
private theorem label_sum_natAdd (M N : AsymPre G X) (i : ℕ) (g : G.G i) (k : Fin (N.n i)) :
    (M.sum N).label i (g, Fin.natAdd (M.n i) k) = N.label i (g, k) := by
  simp [label, sum]

private theorem inclMat_ne_zero {H : Type} [DecidableEq H] {m m' : ℕ} {e : Fin m → Fin m'}
    {a : H × Fin m'} {b : H × Fin m} (h : FreeCat.inclMat e a b ≠ 0) : a = (b.1, e b.2) := by
  by_contra h'
  exact h (by simp [FreeCat.inclMat, h'])

/-- The coordinate inclusion `M → M ⊕ N`. -/
def inl (M N : AsymPre G X) : M ⟶ M.sum N :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inl) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun a b h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.castAdd (N.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact label_sum_castAdd M N i b.1 b.2)

/-- The coordinate inclusion `N → M ⊕ N`. -/
def inr (M N : AsymPre G X) : N ⟶ M.sum N :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inr) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun a b h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.natAdd (M.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact label_sum_natAdd M N i b.1 b.2)

/-- The coordinate projection `M ⊕ N → M`. -/
def fst (M N : AsymPre G X) : M.sum N ⟶ M :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).fst) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun b a h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.castAdd (N.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact (label_sum_castAdd M N i b.1 b.2).symm)

/-- The coordinate projection `M ⊕ N → N`. -/
def snd (M N : AsymPre G X) : M.sum N ⟶ N :=
  homMk (fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).snd) (by
    refine (tendsto_congr fun i => ?_).2 tendsto_const_nhds
    refine prop_eq_zero_of _ _ _ fun b a h => ?_
    have h' : FreeCat.inclMat (G := G.G i) (Fin.natAdd (M.n i)) a b ≠ 0 := h
    rw [inclMat_ne_zero h']
    exact (label_sum_natAdd M N i b.1 b.2).symm)

theorem inl_fst (M N : AsymPre G X) : inl M N ≫ fst M N = 𝟙 M :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inl_fst
theorem inl_snd (M N : AsymPre G X) : inl M N ≫ snd M N = 0 :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inl_snd
theorem inr_fst (M N : AsymPre G X) : inr M N ≫ fst M N = 0 :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inr_fst
theorem inr_snd (M N : AsymPre G X) : inr M N ≫ snd M N = 𝟙 N :=
  hom_ext fun i => (FreeCat.binaryBicone (M.free i) (N.free i)).inr_snd
theorem total (M N : AsymPre G X) :
    fst M N ≫ inl M N + snd M N ≫ inr M N = 𝟙 (M.sum N) :=
  hom_ext fun i => FreeCat.binaryBicone_total (M.free i) (N.free i)

/-- The empty sequence, the zero object. -/
def zero : AsymPre G X where
  n _ := 0
  x _ := Fin.elim0

theorem hom_zero_eq {N : AsymPre G X} (u : (zero : AsymPre G X) ⟶ N) : u = 0 :=
  hom_ext fun _ => FreeCat.hom_ext (Matrix.ext fun _ b => b.2.elim0)

theorem zero_hom_eq {M : AsymPre G X} (u : M ⟶ (zero : AsymPre G X)) : u = 0 :=
  hom_ext fun _ => FreeCat.hom_ext (Matrix.ext fun a _ => a.2.elim0)

end AsymPre

variable (G : GroupSeq p) (X : Type*) [MetricSpace X] [AddAction (ZMod p) X]

/-- Eventual equality of sequences of matrices. -/
def asymRel : HomRel (AsymPre G X) :=
  fun _ _ u v => ∀ᶠ i in atTop, AsymPre.coord u i = AsymPre.coord v i

instance : Congruence (asymRel G X) where
  equivalence :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ h => h.symm,
      fun h₁ h₂ => (h₁.and h₂).mono fun _ h => h.1.trans h.2⟩
  comp_left _ _ _ h := h.mono fun _ h => by simp only [AsymPre.coord_comp, h]
  comp_right _ h := h.mono fun _ h => by simp only [AsymPre.coord_comp, h]

/-- The asymptotic category `𝒜_𝐆(X)`: sequences of equivariant matrices with propagation tending
to `0`, modulo eventual equality. -/
abbrev AsymCat : Type _ := CategoryTheory.Quotient (asymRel G X)

namespace AsymCat

variable {G X}

private theorem rel_add ⦃M N : AsymPre G X⦄ (f₁ f₂ g₁ g₂ : M ⟶ N) (h₁ : asymRel G X f₁ f₂)
    (h₂ : asymRel G X g₁ g₂) : asymRel G X (f₁ + g₁) (f₂ + g₂) :=
  (h₁.and h₂).mono fun _ h => by simp [h.1, h.2]

private theorem rel_smul (c : ℚ) ⦃M N : AsymPre G X⦄ (f₁ f₂ : M ⟶ N)
    (h : asymRel G X f₁ f₂) : asymRel G X (c • f₁) (c • f₂) :=
  h.mono fun _ h => by simp [h]

instance : Preadditive (AsymCat G X) := Quotient.preadditive _ rel_add

instance : (Quotient.functor (asymRel G X)).Additive := Quotient.functor_additive _ rel_add

instance : Linear ℚ (AsymCat G X) := Quotient.linear ℚ _ rel_smul

instance : (Quotient.functor (asymRel G X)).Linear ℚ := Quotient.linear_functor ℚ _ rel_smul

/-- The class `[u]` of a sequence of matrices `u`. -/
abbrev mkHom {M N : AsymPre G X} (u : M ⟶ N) : (⟨M⟩ : AsymCat G X) ⟶ ⟨N⟩ :=
  (Quotient.functor (asymRel G X)).map u

theorem mkHom_eq_iff {M N : AsymPre G X} (u v : M ⟶ N) :
    mkHom u = mkHom v ↔ ∀ᶠ i in atTop, AsymPre.coord u i = AsymPre.coord v i :=
  Quotient.functor_map_eq_iff _ u v

theorem mkHom_surjective {P Q : AsymCat G X} (f : P ⟶ Q) :
    ∃ u : P.as ⟶ Q.as, mkHom u = f :=
  (Quotient.functor (asymRel G X)).map_surjective f

/-- The binary biproduct of `⟨M⟩` and `⟨N⟩`: the concatenation, with the coordinate inclusions and
projections. -/
def binaryBicone (P Q : AsymCat G X) : BinaryBicone P Q where
  pt := ⟨P.as.sum Q.as⟩
  fst := mkHom (AsymPre.fst P.as Q.as)
  snd := mkHom (AsymPre.snd P.as Q.as)
  inl := mkHom (AsymPre.inl P.as Q.as)
  inr := mkHom (AsymPre.inr P.as Q.as)
  inl_fst := by rw [← Functor.map_comp, AsymPre.inl_fst, CategoryTheory.Functor.map_id]; rfl
  inl_snd := by rw [← Functor.map_comp, AsymPre.inl_snd, CategoryTheory.Functor.map_zero]
  inr_fst := by rw [← Functor.map_comp, AsymPre.inr_fst, CategoryTheory.Functor.map_zero]
  inr_snd := by rw [← Functor.map_comp, AsymPre.inr_snd, CategoryTheory.Functor.map_id]; rfl

theorem binaryBicone_total (P Q : AsymCat G X) :
    (binaryBicone P Q).fst ≫ (binaryBicone P Q).inl +
      (binaryBicone P Q).snd ≫ (binaryBicone P Q).inr = 𝟙 (binaryBicone P Q).pt := by
  have h := congrArg (Quotient.functor (asymRel G X)).map (AsymPre.total P.as Q.as)
  rw [CategoryTheory.Functor.map_add, Functor.map_comp, Functor.map_comp,
    CategoryTheory.Functor.map_id] at h
  exact h

theorem isZero_zero : IsZero (⟨AsymPre.zero⟩ : AsymCat G X) := by
  refine ⟨fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Y => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · obtain ⟨u, rfl⟩ := mkHom_surjective f
    rw [AsymPre.hom_zero_eq u]
    exact (Quotient.functor (asymRel G X)).map_zero _ _
  · obtain ⟨u, rfl⟩ := mkHom_surjective f
    rw [AsymPre.zero_hom_eq u]
    exact (Quotient.functor (asymRel G X)).map_zero _ _

instance : HasZeroObject (AsymCat G X) := isZero_zero.hasZeroObject

instance : HasBinaryBiproducts (AsymCat G X) :=
  ⟨fun P Q => hasBinaryBiproduct_of_total (binaryBicone P Q) (binaryBicone_total P Q)⟩

instance : HasFiniteBiproducts (AsymCat G X) := by
  have := hasFiniteProducts_of_has_binary_and_terminal (C := AsymCat G X)
  exact HasFiniteBiproducts.of_hasFiniteProducts

section

/-- The trivial action of `C_2` on a point, for the non-vacuity witness. -/
private abbrev unitAction : AddAction (ZMod 2) Unit := AddAction.compHom Unit (0 : ZMod 2 →+ Unit)

attribute [local instance] unitAction

/-- Non-vacuity: over a one-point space and the trivial group sequence, the object with one
generator at every level is not a zero object (its identity is eventually nonzero). -/
private theorem nonvacuous :
    ¬IsZero (⟨⟨fun _ => 1, fun _ _ => ()⟩⟩ : AsymCat (GroupSeq.trivial 2) Unit) := by
  intro h
  have h2 : mkHom (𝟙 (⟨fun _ => 1, fun _ _ => ()⟩ : AsymPre (GroupSeq.trivial 2) Unit)) =
      mkHom 0 := by
    exact h.eq_of_src _ _
  obtain ⟨i, hi⟩ := ((mkHom_eq_iff _ _).1 h2).exists
  have h3 := congrArg FreeCat.mat hi
  have h4 := congrFun (congrFun h3 (default, ⟨0, Nat.one_pos⟩)) (default, ⟨0, Nat.one_pos⟩)
  simp at h4

end

end AsymCat

end HSP

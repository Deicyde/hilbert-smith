import HilbertSmith.SymmetricForms
import HilbertSmith.TransposeInvolution

/-!
# Forms, duality-preserving functors and Witt classes

The algebra that §6 of OpenAI's preprint uses inside the quotient categories `𝒬_U(X)`: nonsingular
symmetric forms for a duality (`HilbertSmith.Duality`), their adjoints, isometries, negatives,
orthogonal sums and twists, duality-preserving functors, and the three relations on Witt classes
that Propositions 6.4 and 6.7 use. Everything here holds for any additive category with a
duality; no triangulated structure is needed, because §6 never uses a triangle.

* `Form δ`: a nonsingular symmetric form `α : A ⟶ D A`.
* `Form.adj`: the adjoint `R† = α⁻¹ ∘ D(R) ∘ α` of an endomorphism (Lemma 6.2's notation).
* `Form.twist`: the form `α ∘ (2e − 1)` of Definition 6.3, for a self-adjoint idempotent `e`.
* `DualFunctor`, `DualFunctor.mapForm`: duality-preserving functors and the forms they push.
* `WittClasses`: a map from forms to an abelian group, invariant under isometry, additive on
  orthogonal sums, and odd under negation.
* `WittClasses.sum_cls_twist`: for a finite family of orthogonal self-adjoint idempotents summing
  to the identity, `∑ᵢ [α(2eᵢ − 1)] = (2 − m) [α]`. This is the computation in the proof of
  Proposition 6.4, done one pair at a time (`WittClasses.cls_twist_add`) rather than with OpenAI's
  `m × m` involution `S = ∑ⱼ Eⱼ Pⱼ`; the isometry used for a pair is OpenAI's `S` for `m = 2`.
-/

namespace HilbertSmith.Interface

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

section Forms

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A **nonsingular symmetric form** for the duality `δ`: an isomorphism `α : A ⟶ D A` equal to
its transpose. -/
structure Form (δ : Duality C) [δ.D.Additive] where
  /-- The underlying object `A`. -/
  obj : C
  /-- The form `α : A ⟶ D A`. -/
  α : obj ⟶ δ.D.obj (op obj)
  /-- The form is nonsingular. -/
  [isIso : IsIso α]
  /-- The form is symmetric. -/
  symm : δ.IsSymmetric α

attribute [instance] Form.isIso

variable {δ : Duality C} [δ.D.Additive]

namespace Form

/-- The **adjoint** `R† = α⁻¹ ∘ D(R) ∘ α` of an endomorphism `R` of a form (written
diagrammatically: first `α`, then `D(R)`, then `α⁻¹`), as in the proof of Lemma 6.2. -/
noncomputable def adj (φ : Form δ) (R : φ.obj ⟶ φ.obj) : φ.obj ⟶ φ.obj :=
  φ.α ≫ δ.D.map R.op ≫ inv φ.α

/-- `R` is self-adjoint for `φ` exactly when `α ∘ D(R) = R ∘ α`, diagrammatically
`α ≫ D(R) = R ≫ α`. -/
theorem adj_eq_iff (φ : Form δ) (R : φ.obj ⟶ φ.obj) :
    φ.adj R = R ↔ φ.α ≫ δ.D.map R.op = R ≫ φ.α := by
  unfold adj
  constructor
  · intro h
    calc φ.α ≫ δ.D.map R.op = (φ.α ≫ δ.D.map R.op ≫ inv φ.α) ≫ φ.α := by simp
      _ = R ≫ φ.α := by rw [h]
  · intro h; rw [reassoc_of% h]; simp

/-- `R` commutes with `D` through the form, `α ≫ D(R) = R ≫ α`, when it is self-adjoint. -/
theorem comm_of_adj_eq (φ : Form δ) {R : φ.obj ⟶ φ.obj} (h : φ.adj R = R) :
    φ.α ≫ δ.D.map R.op = R ≫ φ.α :=
  (φ.adj_eq_iff R).1 h

/-- The identity commutes with `D` through the form. -/
theorem comm_id (φ : Form δ) : φ.α ≫ δ.D.map (𝟙 φ.obj).op = 𝟙 φ.obj ≫ φ.α := by
  simp

/-- Endomorphisms commuting with `D` through the form are closed under addition. -/
theorem comm_add (φ : Form δ) {R R' : φ.obj ⟶ φ.obj} (h : φ.α ≫ δ.D.map R.op = R ≫ φ.α)
    (h' : φ.α ≫ δ.D.map R'.op = R' ≫ φ.α) :
    φ.α ≫ δ.D.map (R + R').op = (R + R') ≫ φ.α := by
  rw [op_add, δ.D.map_add, Preadditive.comp_add, h, h', Preadditive.add_comp]

/-- Endomorphisms commuting with `D` through the form are closed under subtraction. -/
theorem comm_sub (φ : Form δ) {R R' : φ.obj ⟶ φ.obj} (h : φ.α ≫ δ.D.map R.op = R ≫ φ.α)
    (h' : φ.α ≫ δ.D.map R'.op = R' ≫ φ.α) :
    φ.α ≫ δ.D.map (R - R').op = (R - R') ≫ φ.α := by
  rw [op_sub, δ.D.map_sub, Preadditive.comp_sub, h, h', Preadditive.sub_comp]

/-- Self-adjoint endomorphisms are closed under addition. -/
theorem adj_add (φ : Form δ) {R R' : φ.obj ⟶ φ.obj} (h : φ.adj R = R) (h' : φ.adj R' = R') :
    φ.adj (R + R') = R + R' :=
  (φ.adj_eq_iff _).2 (φ.comm_add (φ.comm_of_adj_eq h) (φ.comm_of_adj_eq h'))

/-- `0` is self-adjoint. -/
theorem adj_zero (φ : Form δ) : φ.adj 0 = 0 := by
  simp [adj]

/-- An **isometry** `φ ≅ ψ`: an isomorphism `f` of the underlying objects with
`α_φ = f ≫ α_ψ ≫ D(f)`, i.e. `φ` is the pullback of `ψ` along `f`. -/
structure Isometry (φ ψ : Form δ) where
  /-- The underlying isomorphism. -/
  iso : φ.obj ≅ ψ.obj
  /-- It carries `ψ` back to `φ`. -/
  comm : φ.α = iso.hom ≫ ψ.α ≫ δ.D.map iso.hom.op

/-- The negative form `(A, -α)`. -/
noncomputable def neg (φ : Form δ) : Form δ where
  obj := φ.obj
  α := -φ.α
  isIso := ⟨-inv φ.α, by simp, by simp⟩
  symm := by
    unfold Duality.IsSymmetric Duality.transpose
    rw [op_neg, δ.D.map_neg, Preadditive.comp_neg]
    exact congrArg Neg.neg φ.symm

section Twist

variable (φ : Form δ) (e : φ.obj ⟶ φ.obj)

/-- `2e − 1` is an involution when `e` is idempotent. -/
theorem twistInvol_comp_self (he : e ≫ e = e) :
    (2 • e - 𝟙 φ.obj) ≫ (2 • e - 𝟙 φ.obj) = 𝟙 φ.obj := by
  simp only [two_nsmul, Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.add_comp,
    Preadditive.comp_add, he, Category.id_comp, Category.comp_id]
  abel

/-- For a self-adjoint `e`, the involution `2e − 1` commutes with `D` through the form. -/
theorem comm_twistInvol (hadj : φ.adj e = e) :
    φ.α ≫ δ.D.map (2 • e - 𝟙 φ.obj).op = (2 • e - 𝟙 φ.obj) ≫ φ.α := by
  have h := φ.comm_of_adj_eq hadj
  rw [two_nsmul]
  exact φ.comm_sub (φ.comm_add h h) φ.comm_id

/-- The **twisted form** `(A, α ∘ (2e − 1))` of Definition 6.3, for a self-adjoint idempotent `e`.
It is nonsingular because `2e − 1` is an involution, and symmetric because that involution is
self-adjoint. -/
noncomputable def twist (he : e ≫ e = e) (hadj : φ.adj e = e) : Form δ where
  obj := φ.obj
  α := (2 • e - 𝟙 φ.obj) ≫ φ.α
  isIso := by
    have : IsIso (2 • e - 𝟙 φ.obj) :=
      ⟨2 • e - 𝟙 φ.obj, twistInvol_comp_self φ e he, twistInvol_comp_self φ e he⟩
    infer_instance
  symm := by
    have hs : δ.biduality.hom.app φ.obj ≫ δ.D.map φ.α.op = φ.α := φ.symm.symm
    unfold Duality.IsSymmetric Duality.transpose
    rw [op_comp, δ.D.map_comp, ← Category.assoc, hs, comm_twistInvol φ e hadj]

end Twist

end Form

section Sum

variable [HasBinaryBiproducts C]

/-- The **orthogonal sum** of two forms, from Deicyde's `Duality.orthSum`. -/
noncomputable def Form.orthSum (φ ψ : Form δ) : Form δ where
  obj := φ.obj ⊞ ψ.obj
  α := δ.orthSum φ.α ψ.α
  isIso := by
    have := (biprod.mapIso (asIso φ.α) (asIso ψ.α)).isIso_hom
    unfold Duality.orthSum
    exact IsIso.comp_isIso' this inferInstance
  symm := δ.orthSum_symm φ.symm ψ.symm

end Sum

section Functors

variable {C' : Type u'} [Category.{v'} C'] [Preadditive C']

/-- A **duality-preserving additive functor** `F : (C, δ) ⟶ (C', δ')`: an additive functor with
a natural isomorphism `η : F ∘ D ≅ D' ∘ F` compatible with the two bidualities. Proposition 2.5
says that direct images `g_*` of test categories are of this kind ("they commute coherently with
Verdier duality"). -/
structure DualFunctor (δ : Duality C) [δ.D.Additive] (δ' : Duality C') [δ'.D.Additive] where
  /-- The functor. -/
  F : C ⥤ C'
  /-- It is additive. -/
  [additive : F.Additive]
  /-- The comparison `F(D A) ≅ D'(F A)`. -/
  η : δ.D ⋙ F ≅ F.op ⋙ δ'.D
  /-- Compatibility with biduality. -/
  bidual : ∀ X : C, F.map (δ.biduality.hom.app X) ≫ η.hom.app (op (δ.D.obj (op X))) =
    δ'.biduality.hom.app (F.obj X) ≫ δ'.D.map (η.hom.app (op X)).op

attribute [instance] DualFunctor.additive

variable {δ' : Duality C'} [δ'.D.Additive]

/-- The form `(F A, F α ≫ η)` pushed along a duality-preserving functor. -/
noncomputable def DualFunctor.mapForm (Φ : DualFunctor δ δ') (φ : Form δ) : Form δ' where
  obj := Φ.F.obj φ.obj
  α := Φ.F.map φ.α ≫ Φ.η.hom.app (op φ.obj)
  isIso := inferInstance
  symm := by
    have hnat := Φ.η.hom.naturality φ.α.op
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hnat
    unfold Duality.IsSymmetric Duality.transpose
    rw [op_comp, δ'.D.map_comp, ← Category.assoc, ← Φ.bidual, Category.assoc, ← hnat,
      ← Category.assoc, ← Φ.F.map_comp]
    exact congrArg (fun x => Φ.F.map x ≫ Φ.η.hom.app (op φ.obj)) φ.symm

end Functors

/-- **The relations on Witt classes that §6 uses**, for a group `W` receiving classes of forms:
isometric forms have equal classes, orthogonal sums add, and negation negates. They hold for the
Witt group of any category with duality in which `2` is invertible (OpenAI's coefficients are
`ℝ`): an isometry identifies the forms, the orthogonal sum is the group law, and
`(A, α) ⊥ (A, −α)` is neutral. The proofs of Propositions 6.4 and 6.7 use nothing else about
`W_d(𝒬_U(X))` (06:262-291, 06:437-442). -/
structure WittClasses (δ : Duality C) [δ.D.Additive] [HasBinaryBiproducts C] (W : Type*)
    [AddCommGroup W] where
  /-- The class of a form. -/
  cls : Form δ → W
  /-- Isometric forms have equal classes. -/
  cls_isometry : ∀ {φ ψ : Form δ}, φ.Isometry ψ → cls φ = cls ψ
  /-- Orthogonal sums add. -/
  cls_orthSum : ∀ φ ψ : Form δ, cls (φ.orthSum ψ) = cls φ + cls ψ
  /-- `[A, −α] = −[A, α]`. -/
  cls_neg : ∀ φ : Form δ, cls φ.neg = -cls φ

namespace Form

variable {φ ψ : Form δ}

/-- An isometry carries a twisted form to the twisted form of the conjugated idempotent. Used for
Proposition 6.7, where the isometry is multiplication by the sheet multiplier `β`. -/
noncomputable def Isometry.twist (σ : φ.Isometry ψ) {e : φ.obj ⟶ φ.obj} {e' : ψ.obj ⟶ ψ.obj}
    (he : e ≫ e = e) (hadj : φ.adj e = e) (he' : e' ≫ e' = e') (hadj' : ψ.adj e' = e')
    (hconj : σ.iso.inv ≫ e ≫ σ.iso.hom = e') :
    (φ.twist e he hadj).Isometry (ψ.twist e' he' hadj') where
  iso := σ.iso
  comm := by
    subst hconj
    change (2 • e - 𝟙 φ.obj) ≫ φ.α = σ.iso.hom ≫
      ((2 • (σ.iso.inv ≫ e ≫ σ.iso.hom) - 𝟙 ψ.obj) ≫ ψ.α) ≫ δ.D.map σ.iso.hom.op
    rw [σ.comm]
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp]

end Form

section Functors

variable {C' : Type u'} [Category.{v'} C'] [Preadditive C'] {δ' : Duality C'} [δ'.D.Additive]

/-- Pushing a twisted form along a duality-preserving functor, then transporting it along an
isometry of the pushed form, gives the twisted form of the transported idempotent. Used for
Proposition 6.5. -/
noncomputable def DualFunctor.mapFormTwist (Φ : DualFunctor δ δ') {φ : Form δ} {ψ : Form δ'}
    (σ : (Φ.mapForm φ).Isometry ψ) {e : φ.obj ⟶ φ.obj} {e' : ψ.obj ⟶ ψ.obj}
    (he : e ≫ e = e) (hadj : φ.adj e = e) (he' : e' ≫ e' = e') (hadj' : ψ.adj e' = e')
    (hconj : σ.iso.inv ≫ Φ.F.map e ≫ σ.iso.hom = e') :
    (Φ.mapForm (φ.twist e he hadj)).Isometry (ψ.twist e' he' hadj') where
  iso := σ.iso
  comm := by
    subst hconj
    -- State the identity for an arbitrary `s : F A ≅ B`, so that no `mapForm` appears in types.
    have key : ∀ s : Φ.F.obj φ.obj ≅ ψ.obj,
        Φ.F.map φ.α ≫ Φ.η.hom.app (op φ.obj) = s.hom ≫ ψ.α ≫ δ'.D.map s.hom.op →
        Φ.F.map ((2 • e - 𝟙 φ.obj) ≫ φ.α) ≫ Φ.η.hom.app (op φ.obj) =
          s.hom ≫ ((2 • (s.inv ≫ Φ.F.map e ≫ s.hom) - 𝟙 ψ.obj) ≫ ψ.α) ≫ δ'.D.map s.hom.op := by
      intro s hs
      rw [Φ.F.map_comp, Φ.F.map_sub, Φ.F.map_nsmul, Φ.F.map_id, Category.assoc, hs]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.nsmul_comp,
        Preadditive.comp_nsmul, Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp]
    exact key σ.iso σ.comm

end Functors

section Involution

variable [HasBinaryBiproducts C]

/-- The first component of `D(X ⊞ Y) ≅ DX ⊞ DY` is `D(inl)`. -/
theorem dualBiprodIso_hom_fst (X Y : C) :
    (δ.dualBiprodIso X Y).hom ≫ biprod.fst = δ.D.map biprod.inl.op := by
  simp [Duality.dualBiprodIso, Duality.dualBiprodHom]

/-- The second component of `D(X ⊞ Y) ≅ DX ⊞ DY` is `D(inr)`. -/
theorem dualBiprodIso_hom_snd (X Y : C) :
    (δ.dualBiprodIso X Y).hom ≫ biprod.snd = δ.D.map biprod.inr.op := by
  simp [Duality.dualBiprodIso, Duality.dualBiprodHom]

/-- The inverse of `D(X ⊞ Y) ≅ DX ⊞ DY` restricts to `D(fst)` on `DX`. -/
@[reassoc]
theorem inl_dualBiprodIso_inv (X Y : C) :
    biprod.inl ≫ (δ.dualBiprodIso X Y).inv = δ.D.map biprod.fst.op := by
  simp [Duality.dualBiprodIso, Duality.dualBiprodInv]

/-- The inverse of `D(X ⊞ Y) ≅ DX ⊞ DY` restricts to `D(snd)` on `DY`. -/
@[reassoc]
theorem inr_dualBiprodIso_inv (X Y : C) :
    biprod.inr ≫ (δ.dualBiprodIso X Y).inv = δ.D.map biprod.snd.op := by
  simp [Duality.dualBiprodIso, Duality.dualBiprodInv]

/-- An orthogonal sum of precomposed forms is the precomposed orthogonal sum. -/
theorem orthSum_comp {X Y : C} (P : X ⟶ X) (Q : Y ⟶ Y) (α : X ⟶ δ.D.obj (op X))
    (β : Y ⟶ δ.D.obj (op Y)) :
    δ.orthSum (P ≫ α) (Q ≫ β) = biprod.map P Q ≫ δ.orthSum α β := by
  unfold Duality.orthSum
  rw [← Category.assoc, map_comp_map]

/-- **Adjoints on `A ⊞ A`.** For an endomorphism `S` of `A ⊞ A`, `(α ⊥ α) ≫ D(S) = S ≫ (α ⊥ α)`
as soon as each entry `S_{ji}` (from the `i`-th to the `j`-th summand) is adjoint to `S_{ij}`
for `α`: the adjoint for `α ⊥ α` is the transposed matrix of adjoints. -/
theorem Form.orthSum_comp_map_op (φ : Form δ) (S : φ.obj ⊞ φ.obj ⟶ φ.obj ⊞ φ.obj)
    (h₁₁ : φ.α ≫ δ.D.map (biprod.inl ≫ S ≫ biprod.fst).op =
      (biprod.inl ≫ S ≫ biprod.fst) ≫ φ.α)
    (h₁₂ : φ.α ≫ δ.D.map (biprod.inr ≫ S ≫ biprod.fst).op =
      (biprod.inl ≫ S ≫ biprod.snd) ≫ φ.α)
    (h₂₁ : φ.α ≫ δ.D.map (biprod.inl ≫ S ≫ biprod.snd).op =
      (biprod.inr ≫ S ≫ biprod.fst) ≫ φ.α)
    (h₂₂ : φ.α ≫ δ.D.map (biprod.inr ≫ S ≫ biprod.snd).op =
      (biprod.inr ≫ S ≫ biprod.snd) ≫ φ.α) :
    δ.orthSum φ.α φ.α ≫ δ.D.map S.op = S ≫ δ.orthSum φ.α φ.α := by
  rw [← cancel_mono (δ.dualBiprodIso φ.obj φ.obj).hom]
  unfold Duality.orthSum
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, biprod.inl_map_assoc,
      biprod.inr_map_assoc, biprod.map_fst, biprod.map_snd, dualBiprodIso_hom_fst,
      dualBiprodIso_hom_snd, inl_dualBiprodIso_inv_assoc, inr_dualBiprodIso_inv_assoc,
      ← δ.D.map_comp, ← op_comp]
  · simpa only [Category.assoc] using h₁₁
  · simpa only [Category.assoc] using h₁₂
  · simpa only [Category.assoc] using h₂₁
  · simpa only [Category.assoc] using h₂₂

/-- OpenAI's involution `S = [[1 − f, f], [f, 1 − f]]` on `A ⊞ A`, used in the proof of
Proposition 6.4 for `m = 2` (see `WittClasses.cls_twist_add`). -/
noncomputable def twistSwap {A : C} (f : A ⟶ A) : A ⊞ A ⟶ A ⊞ A :=
  biprod.lift (biprod.fst ≫ (𝟙 A - f) + biprod.snd ≫ f) (biprod.fst ≫ f + biprod.snd ≫ (𝟙 A - f))

@[reassoc (attr := simp)]
theorem inl_twistSwap {A : C} (f : A ⟶ A) :
    biprod.inl ≫ twistSwap f = biprod.lift (𝟙 A - f) f := by
  simp [twistSwap, comp_lift]

@[reassoc (attr := simp)]
theorem inr_twistSwap {A : C} (f : A ⟶ A) :
    biprod.inr ≫ twistSwap f = biprod.lift f (𝟙 A - f) := by
  simp [twistSwap, comp_lift]

@[reassoc (attr := simp)]
theorem twistSwap_fst {A : C} (f : A ⟶ A) :
    twistSwap f ≫ biprod.fst = biprod.fst ≫ (𝟙 A - f) + biprod.snd ≫ f := by
  simp [twistSwap]

@[reassoc (attr := simp)]
theorem twistSwap_snd {A : C} (f : A ⟶ A) :
    twistSwap f ≫ biprod.snd = biprod.fst ≫ f + biprod.snd ≫ (𝟙 A - f) := by
  simp [twistSwap]

/-- `S² = 1` when `f` is idempotent. -/
theorem twistSwap_comp_self {A : C} {f : A ⟶ A} (hf : f ≫ f = f) :
    twistSwap f ≫ twistSwap f = 𝟙 (A ⊞ A) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.sub_comp, hf]

end Involution

namespace WittClasses

variable [HasBinaryBiproducts C] {W : Type*} [AddCommGroup W] (w : WittClasses δ W)

/-- The class of a twisted form depends only on the idempotent, not on the proofs that it is a
self-adjoint idempotent. -/
theorem cls_twist_congr (φ : Form δ) {e e' : φ.obj ⟶ φ.obj} (h : e = e') (he : e ≫ e = e)
    (hadj : φ.adj e = e) (he' : e' ≫ e' = e') (hadj' : φ.adj e' = e') :
    w.cls (φ.twist e he hadj) = w.cls (φ.twist e' he' hadj') := by
  subst h
  rfl

/-- The twist by `0` is the negative form. -/
theorem cls_twist_zero (φ : Form δ) (h₀ : (0 : φ.obj ⟶ φ.obj) ≫ 0 = 0) (h₁ : φ.adj 0 = 0) :
    w.cls (φ.twist 0 h₀ h₁) = -w.cls φ := by
  have σ : (φ.twist 0 h₀ h₁).Isometry φ.neg :=
    { iso := Iso.refl _
      comm := by
        change (2 • (0 : φ.obj ⟶ φ.obj) - 𝟙 φ.obj) ≫ φ.α = 𝟙 φ.obj ≫ (-φ.α) ≫ δ.D.map (𝟙 _).op
        simp }
  rw [w.cls_isometry σ, w.cls_neg]

/-- The twist by `1` is the form itself. -/
theorem cls_twist_id (φ : Form δ) (h₀ : 𝟙 φ.obj ≫ 𝟙 φ.obj = 𝟙 φ.obj)
    (h₁ : φ.adj (𝟙 φ.obj) = 𝟙 φ.obj) :
    w.cls (φ.twist (𝟙 φ.obj) h₀ h₁) = w.cls φ := by
  refine w.cls_isometry { iso := Iso.refl _, comm := ?_ }
  change (2 • 𝟙 φ.obj - 𝟙 φ.obj) ≫ φ.α = 𝟙 φ.obj ≫ φ.α ≫ δ.D.map (𝟙 _).op
  simp [two_nsmul]

/-- **Two orthogonal projectors.** For orthogonal self-adjoint idempotents `e`, `f`,
`[α(2e − 1)] + [α(2f − 1)] = [α(2(e + f) − 1)] − [α]`. The isometry is
`S = [[1 − f, f], [f, 1 − f]]` on `A ⊕ A`, from `(A, α(2e − 1)) ⊥ (A, α(2f − 1))` to
`(A, α(2(e + f) − 1)) ⊥ (A, −α)`: it is self-adjoint, `S² = 1`, and `S Q' S = Q` for the two
diagonal involutions, which is OpenAI's computation in the proof of Proposition 6.4 for `m = 2`
(06:264-288). -/
theorem cls_twist_add (φ : Form δ) {e f : φ.obj ⟶ φ.obj} (he : e ≫ e = e) (hf : f ≫ f = f)
    (hef : e ≫ f = 0) (hfe : f ≫ e = 0) (hae : φ.adj e = e) (haf : φ.adj f = f)
    (hg : (e + f) ≫ (e + f) = e + f) (hag : φ.adj (e + f) = e + f) :
    w.cls (φ.twist e he hae) + w.cls (φ.twist f hf haf) =
      w.cls (φ.twist (e + f) hg hag) - w.cls φ := by
  -- The matrix identity `S Q' S = Q` for the diagonal involutions `Q'` and `Q`.
  have hmat : twistSwap f ≫ biprod.map (2 • (e + f) - 𝟙 φ.obj) (-𝟙 φ.obj) ≫ twistSwap f =
      biprod.map (2 • e - 𝟙 φ.obj) (2 • f - 𝟙 φ.obj) := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_sub,
        Preadditive.sub_comp, two_nsmul, hf, hef, hfe] <;> abel
  -- `S` is self-adjoint for `α ⊥ α`.
  have hS : δ.orthSum φ.α φ.α ≫ δ.D.map (twistSwap f).op =
      twistSwap f ≫ δ.orthSum φ.α φ.α := by
    apply φ.orthSum_comp_map_op <;> simpa using φ.comm_of_adj_eq haf
  let σ : ((φ.twist e he hae).orthSum (φ.twist f hf haf)).Isometry
      ((φ.twist (e + f) hg hag).orthSum φ.neg) :=
    { iso := ⟨twistSwap f, twistSwap f, twistSwap_comp_self hf, twistSwap_comp_self hf⟩
      comm := by
        change δ.orthSum ((2 • e - 𝟙 φ.obj) ≫ φ.α) ((2 • f - 𝟙 φ.obj) ≫ φ.α) =
          twistSwap f ≫ δ.orthSum ((2 • (e + f) - 𝟙 φ.obj) ≫ φ.α) (-φ.α) ≫
            δ.D.map (twistSwap f).op
        rw [show -φ.α = (-𝟙 φ.obj) ≫ φ.α by simp, orthSum_comp, orthSum_comp,
          Category.assoc, hS, ← hmat]
        simp only [Category.assoc] }
  rw [← w.cls_orthSum, w.cls_isometry σ, w.cls_orthSum, w.cls_neg, sub_eq_add_neg]

/-- **The computation in Proposition 6.4.** For a finite family `e₀, …, e_{m−1}` of pairwise
orthogonal self-adjoint idempotents with `∑ eᵢ = 1` (the identities (6.6)),
`∑ᵢ [α(2eᵢ − 1)] = (2 − m) [α]`. By induction over the finite set of indices, merging one
projector at a time with `cls_twist_add`. -/
theorem sum_cls_twist (φ : Form δ) {m : ℕ} (e : Fin m → (φ.obj ⟶ φ.obj))
    (hidem : ∀ i, e i ≫ e i = e i) (horth : ∀ i j, i ≠ j → e i ≫ e j = 0)
    (hsum : ∑ i, e i = 𝟙 φ.obj) (hadj : ∀ i, φ.adj (e i) = e i) :
    ∑ i, w.cls (φ.twist (e i) (hidem i) (hadj i)) = ((2 : ℤ) - m) • w.cls φ := by
  classical
  -- Invariant: the partial sum `E_s = ∑_{i ∈ s} eᵢ` is a self-adjoint idempotent and
  -- `∑_{i ∈ s} [α(2eᵢ − 1)] = [α(2E_s − 1)] − |s| [α] + [α]`.
  have key : ∀ s : Finset (Fin m), ∃ (hs : (∑ i ∈ s, e i) ≫ (∑ i ∈ s, e i) = ∑ i ∈ s, e i)
      (ha : φ.adj (∑ i ∈ s, e i) = ∑ i ∈ s, e i),
      ∑ i ∈ s, w.cls (φ.twist (e i) (hidem i) (hadj i)) =
        w.cls (φ.twist _ hs ha) - s.card • w.cls φ + w.cls φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hs0 : (∑ i ∈ (∅ : Finset (Fin m)), e i) ≫ ∑ i ∈ ∅, e i = ∑ i ∈ ∅, e i := by
        rw [Finset.sum_empty, comp_zero]
      have ha0 : φ.adj (∑ i ∈ (∅ : Finset (Fin m)), e i) = ∑ i ∈ ∅, e i := by
        rw [Finset.sum_empty]
        exact φ.adj_zero
      refine ⟨hs0, ha0, ?_⟩
      rw [Finset.sum_empty, w.cls_twist_congr φ Finset.sum_empty hs0 ha0 comp_zero φ.adj_zero,
        cls_twist_zero]
      simp
    | insert j s hj ih =>
      obtain ⟨hs, ha, h⟩ := ih
      have hjs : e j ≫ ∑ i ∈ s, e i = 0 := by
        rw [Preadditive.comp_sum]
        exact Finset.sum_eq_zero fun i hi => horth j i fun hji => hj (hji ▸ hi)
      have hsj : (∑ i ∈ s, e i) ≫ e j = 0 := by
        rw [Preadditive.sum_comp]
        exact Finset.sum_eq_zero fun i hi => horth i j fun hij => hj (hij ▸ hi)
      have hg : (e j + ∑ i ∈ s, e i) ≫ (e j + ∑ i ∈ s, e i) = e j + ∑ i ∈ s, e i := by
        simp [Preadditive.add_comp, Preadditive.comp_add, hidem, hs, hjs, hsj]
      have hag : φ.adj (e j + ∑ i ∈ s, e i) = e j + ∑ i ∈ s, e i := φ.adj_add (hadj j) ha
      have hins : ∑ i ∈ insert j s, e i = e j + ∑ i ∈ s, e i := Finset.sum_insert hj
      refine ⟨hins ▸ hg, hins ▸ hag, ?_⟩
      rw [Finset.sum_insert hj, h, ← add_assoc, add_sub_assoc',
        w.cls_twist_add φ (hidem j) hs hjs hsj (hadj j) ha hg hag,
        w.cls_twist_congr φ hins.symm hg hag (hins ▸ hg) (hins ▸ hag),
        Finset.card_insert_of_notMem hj, succ_nsmul]
      abel
  obtain ⟨hs, ha, h⟩ := key Finset.univ
  rw [h, w.cls_twist_congr φ hsum hs ha (by simp) (by simp [Form.adj]), cls_twist_id,
    Finset.card_univ, Fintype.card_fin, sub_smul, natCast_zsmul]
  abel

end WittClasses

end Forms

end HilbertSmith.Interface

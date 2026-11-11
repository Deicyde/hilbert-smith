import Mathlib
import HilbertSmithPaper.LTheory.Base.Categories.DualityCategory

/-!
# Free category of a finite group

For a finite group `G` (written additively), the duality category `Free(ℚ[G])`:
* an object is a number `n ∈ ℕ` (`HSP.FreeCat G`, a structure with one field `n`); its basis is the
  free `G`-set `G × Fin n`, with `G` acting on the first factor;
* a morphism `n → m` is a `G`-equivariant rational matrix `u ∈ ℚ^{(G × Fin m) × (G × Fin n)}`,
  `u (g + h, k') (g + h', k) = u (h, k') (h', k)` (`HSP.FreeCat.equivariant`, a `ℚ`-submodule of
  the matrices); composition is the matrix product (`f ≫ g` is `g * f`) and the identity is the
  identity matrix;
* the sum of `n` and `m` is `n + m`, with the coordinate inclusions and projections
  (`Fin.castAdd`, `Fin.natAdd`); the zero object is `0`;
* the duality is strict: `n^* = n` and `u^* = uᵀ` (`HSP.FreeCat.dualCat`).

The group needs `[AddGroup G] [Fintype G] [DecidableEq G]` (decidable equality for identity
matrices), as in `HSP.GroupSeq`. For `G = Unit` this is `Free(ℚ)`; a private witness checks that
`DualCat (FreeCat Unit)` is inhabited.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

/-- The objects of `Free(ℚ[G])`: a number `n`, standing for the based free module on `G × Fin n`. -/
structure FreeCat (G : Type) where
  /-- The rank `n`. -/
  n : ℕ

namespace FreeCat

variable (G : Type) [AddGroup G]

/-- The `G`-equivariant matrices `u ∈ ℚ^{(G × Fin m) × (G × Fin n)}`:
`u (g + h, k') (g + h', k) = u (h, k') (h', k)` for all `g`. -/
def equivariant (m n : ℕ) : Submodule ℚ (Matrix (G × Fin m) (G × Fin n) ℚ) where
  carrier := {u | ∀ g h h' k' k, u (g + h, k') (g + h', k) = u (h, k') (h', k)}
  add_mem' {u v} hu hv g h h' k' k := by simp [hu g h h' k' k, hv g h h' k' k]
  zero_mem' _ _ _ _ _ := rfl
  smul_mem' c u hu g h h' k' k := by simp [hu g h h' k' k]

variable {G}

theorem one_mem [DecidableEq G] (n : ℕ) : (1 : Matrix (G × Fin n) (G × Fin n) ℚ) ∈ equivariant G n n := by
  intro g h h' k' k
  simp only [Matrix.one_apply, Prod.mk.injEq, add_right_inj]

theorem mul_mem [Fintype G] {l m n : ℕ} {v : Matrix (G × Fin l) (G × Fin m) ℚ}
    {u : Matrix (G × Fin m) (G × Fin n) ℚ} (hv : v ∈ equivariant G l m)
    (hu : u ∈ equivariant G m n) : v * u ∈ equivariant G l n := by
  intro g h h' k' k
  simp only [Matrix.mul_apply]
  refine (Fintype.sum_equiv ((Equiv.addLeft g).prodCongr (Equiv.refl _)) _ _ fun c => ?_).symm
  obtain ⟨a, j⟩ := c
  simp only [Equiv.prodCongr_apply, Equiv.coe_addLeft, Equiv.coe_refl, Prod.map_apply, id_eq]
  rw [hv g h a k' j, hu g a h' j k]

theorem transpose_mem {m n : ℕ} {u : Matrix (G × Fin m) (G × Fin n) ℚ}
    (hu : u ∈ equivariant G m n) : u.transpose ∈ equivariant G n m :=
  fun g h h' k' k => hu g h' h k k'

instance : Quiver (FreeCat G) where
  Hom M N := equivariant G N.n M.n

instance (M N : FreeCat G) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs (AddCommGroup (equivariant G N.n M.n))

instance (M N : FreeCat G) : Module ℚ (M ⟶ N) :=
  inferInstanceAs (Module ℚ (equivariant G N.n M.n))

/-- The underlying matrix of a morphism. -/
def mat {M N : FreeCat G} (u : M ⟶ N) : Matrix (G × Fin N.n) (G × Fin M.n) ℚ :=
  Subtype.val (p := fun u => u ∈ equivariant G N.n M.n) u

@[ext]
theorem hom_ext {M N : FreeCat G} {u v : M ⟶ N} (h : mat u = mat v) : u = v := Subtype.ext h

@[simp] theorem mat_add {M N : FreeCat G} (u v : M ⟶ N) : mat (u + v) = mat u + mat v := rfl
@[simp] theorem mat_zero {M N : FreeCat G} : mat (0 : M ⟶ N) = 0 := rfl
@[simp] theorem mat_neg {M N : FreeCat G} (u : M ⟶ N) : mat (-u) = -mat u := rfl
@[simp] theorem mat_sub {M N : FreeCat G} (u v : M ⟶ N) : mat (u - v) = mat u - mat v := rfl
@[simp] theorem mat_smul {M N : FreeCat G} (c : ℚ) (u : M ⟶ N) : mat (c • u) = c • mat u := rfl

/-- A morphism from an equivariant matrix. -/
def ofMat {M N : FreeCat G} (u : Matrix (G × Fin N.n) (G × Fin M.n) ℚ)
    (hu : u ∈ equivariant G N.n M.n) : M ⟶ N := ⟨u, hu⟩

@[simp] theorem ofMat_mat {M N : FreeCat G} (u : M ⟶ N) : ofMat (mat u) u.2 = u := rfl

@[simp] theorem mat_ofMat {M N : FreeCat G} (u : Matrix (G × Fin N.n) (G × Fin M.n) ℚ)
    (hu : u ∈ equivariant G N.n M.n) : mat (ofMat u hu) = u := rfl

variable [Fintype G] [DecidableEq G]

instance : Category (FreeCat G) where
  id M := ofMat 1 (one_mem M.n)
  comp f g := ofMat (mat g * mat f) (mul_mem g.2 f.2)
  id_comp _ := hom_ext (Matrix.mul_one _)
  comp_id _ := hom_ext (Matrix.one_mul _)
  assoc _ _ _ := hom_ext (Matrix.mul_assoc _ _ _).symm

@[simp] theorem mat_id (M : FreeCat G) : mat (𝟙 M) = 1 := rfl
@[simp] theorem mat_comp {M N P : FreeCat G} (f : M ⟶ N) (g : N ⟶ P) :
    mat (f ≫ g) = mat g * mat f := rfl

instance : Preadditive (FreeCat G) where
  add_comp _ _ _ f f' g := hom_ext (Matrix.mul_add _ _ _)
  comp_add _ _ _ f g g' := hom_ext (Matrix.add_mul _ _ _)

instance : Linear ℚ (FreeCat G) where
  smul_comp _ _ _ c f g := hom_ext (Matrix.mul_smul _ _ _)
  comp_smul _ _ _ f c g := hom_ext (Matrix.smul_mul _ _ _)

/-! ### Sums -/

/-- The coordinate inclusion of a basis `G × Fin m` into `G × Fin m'` along `e : Fin m → Fin m'`,
as a matrix with rows indexed by `G × Fin m'`. -/
private def incl {m m' : ℕ} (e : Fin m → Fin m') : Matrix (G × Fin m') (G × Fin m) ℚ :=
  fun a b => if a = (b.1, e b.2) then 1 else 0

omit [Fintype G] in
private theorem incl_mem {m m' : ℕ} (e : Fin m → Fin m') :
    incl (G := G) e ∈ equivariant G m' m := by
  intro g h h' k' k
  simp [incl]

omit [AddGroup G] [Fintype G] in
private theorem incl_apply_of_inj {m m' : ℕ} {e : Fin m → Fin m'} (he : Function.Injective e)
    (g : G) (k : Fin m) (b : G × Fin m) :
    incl e (g, e k) b = if b = (g, k) then 1 else 0 := by
  obtain ⟨g', k'⟩ := b
  simp only [incl, Prod.mk.injEq, he.eq_iff]
  by_cases h1 : g = g' <;> by_cases h2 : k = k' <;> simp [h1, h2, eq_comm]

omit [AddGroup G] in
private theorem incl_transpose_mul {m m' m'' : ℕ} (e : Fin m → Fin m'') (e' : Fin m' → Fin m'') :
    (incl (G := G) e).transpose * incl (G := G) e' =
      ((fun p q => if ((p.1, e p.2) : G × Fin m'') = (q.1, e' q.2) then 1 else 0 :
        Matrix (G × Fin m) (G × Fin m') ℚ)) := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, incl, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ]
  simp

private theorem castAdd_ne_natAdd {m n : ℕ} (k : Fin m) (k' : Fin n) :
    Fin.castAdd n k ≠ Fin.natAdd m k' := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

omit [AddGroup G] in
private theorem incl_mul_transpose_of_inj {m m' : ℕ} {e : Fin m → Fin m'}
    (he : Function.Injective e) (g : G) (k : Fin m) (a' : G × Fin m') :
    (incl (G := G) e * (incl (G := G) e).transpose) (g, e k) a' =
      if a' = (g, e k) then 1 else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, incl_apply_of_inj he, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ]
  simp [incl]

omit [AddGroup G] in
private theorem incl_mul_transpose_of_not {m m' : ℕ} {e : Fin m → Fin m'} (g : G) (j : Fin m')
    (hj : ∀ k, j ≠ e k) (a' : G × Fin m') :
    (incl (G := G) e * (incl (G := G) e).transpose) (g, j) a' = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  simp only [Matrix.transpose_apply, incl, Prod.mk.injEq]
  split_ifs with h <;> first | exact absurd h.2 (hj _) | simp

omit [AddGroup G] in
private theorem incl_total (m n : ℕ) :
    incl (G := G) (Fin.castAdd n : Fin m → Fin (m + n)) *
        (incl (G := G) (Fin.castAdd n : Fin m → Fin (m + n))).transpose +
      incl (G := G) (Fin.natAdd m : Fin n → Fin (m + n)) *
        (incl (G := G) (Fin.natAdd m : Fin n → Fin (m + n))).transpose =
        (1 : Matrix (G × Fin (m + n)) (G × Fin (m + n)) ℚ) := by
  ext ⟨g, j⟩ a'
  rw [Matrix.add_apply, Matrix.one_apply]
  induction j using Fin.addCases with
  | left k =>
    rw [incl_mul_transpose_of_inj (Fin.castAdd_injective m n),
      incl_mul_transpose_of_not _ _ (fun k' => castAdd_ne_natAdd k k'), add_zero]
    simp only [eq_comm]
  | right k =>
    rw [incl_mul_transpose_of_inj (Fin.natAdd_injective n m),
      incl_mul_transpose_of_not _ _ (fun k' h => castAdd_ne_natAdd k' k h.symm), zero_add]
    simp only [eq_comm]

/-- The binary biproduct `n ⊕ m = n + m`, with the coordinate inclusions and projections. -/
private def binaryBicone (M N : FreeCat G) : BinaryBicone M N where
  pt := ⟨M.n + N.n⟩
  fst := ofMat (incl (Fin.castAdd N.n)).transpose (transpose_mem (incl_mem _))
  snd := ofMat (incl (Fin.natAdd M.n)).transpose (transpose_mem (incl_mem _))
  inl := ofMat (incl (Fin.castAdd N.n)) (incl_mem _)
  inr := ofMat (incl (Fin.natAdd M.n)) (incl_mem _)
  inl_fst := hom_ext (by
    rw [mat_comp, mat_ofMat, mat_ofMat, incl_transpose_mul]
    ext p q; simp [Matrix.one_apply, Prod.ext_iff, (Fin.castAdd_injective _ _).eq_iff])
  inl_snd := hom_ext (by
    rw [mat_comp, mat_ofMat, mat_ofMat, incl_transpose_mul, mat_zero]
    ext p q
    exact ite_eq_right_iff.2 fun h => absurd (Prod.ext_iff.1 h).2.symm (castAdd_ne_natAdd _ _))
  inr_fst := hom_ext (by
    rw [mat_comp, mat_ofMat, mat_ofMat, incl_transpose_mul, mat_zero]
    ext p q
    exact ite_eq_right_iff.2 fun h => absurd (Prod.ext_iff.1 h).2 (castAdd_ne_natAdd _ _))
  inr_snd := hom_ext (by
    rw [mat_comp, mat_ofMat, mat_ofMat, incl_transpose_mul]
    ext p q; simp [Matrix.one_apply, Prod.ext_iff, (Fin.natAdd_injective _ _).eq_iff])

/-- The zero object of `Free(ℚ[G])` is `0`. -/
theorem isZero_zero : IsZero (⟨0⟩ : FreeCat G) := by
  refine ⟨fun Y => ⟨⟨⟨0⟩, fun f => hom_ext (Matrix.ext fun _ b => b.2.elim0)⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => hom_ext (Matrix.ext fun a _ => a.2.elim0)⟩⟩⟩

instance : HasZeroObject (FreeCat G) := isZero_zero.hasZeroObject

instance : HasBinaryBiproducts (FreeCat G) :=
  ⟨fun M N => hasBinaryBiproduct_of_total (binaryBicone M N)
    (hom_ext (incl_total M.n N.n))⟩

instance : HasFiniteBiproducts (FreeCat G) := by
  have := hasFiniteProducts_of_has_binary_and_terminal (C := FreeCat G)
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- `Free(ℚ[G])` is a strict duality category under `n^* = n` and `u^* = uᵀ`. -/
instance dualCat : DualCat (FreeCat G) where
  dual M := M
  dualHom u := ofMat (mat u).transpose (transpose_mem u.2)
  dualHom_id M := hom_ext Matrix.transpose_one
  dualHom_comp f g := hom_ext (Matrix.transpose_mul _ _)
  dualHom_add f g := hom_ext (Matrix.transpose_add _ _)
  dualHom_smul c f := hom_ext (Matrix.transpose_smul _ _)
  dual_dual _ := rfl
  dualHom_dualHom f := hom_ext (by simp)
  dualHom_zero := hom_ext (Matrix.transpose_zero)
  dualHom_neg f := hom_ext (Matrix.transpose_neg _)
  dualHom_sub f g := hom_ext (Matrix.transpose_sub _ _)
  dualHom_eqToHom h := by subst h; exact hom_ext (by simp)

@[simp] theorem mat_dualHom {M N : FreeCat G} (u : M ⟶ N) :
    mat (DualCat.dualHom u) = (mat u).transpose := rfl

private theorem nonvacuous : Nonempty (DualCat (FreeCat Unit)) := ⟨inferInstance⟩

end FreeCat

end HSP

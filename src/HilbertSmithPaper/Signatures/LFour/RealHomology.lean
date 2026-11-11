import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.FreeCategory
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiDuality

/-!
# Real homology

For a chain complex `C` in `Kar Free(ℚ[G])` with `C_r = (n_r, e_r)`, the real chains are
`C_r(ℝ) = im(e_r) ⊆ ℝ^{G × Fin n_r}` with the real matrices of the differentials, and
`H_r(C; ℝ)` (`HSP.realH C r`) is the homology of this real complex in degree `r`: the real cycles
`im(e_r) ∩ ker d_r` modulo the real boundaries `d_{r+1}(im e_{r+1})`. A chain map `f` induces
`f_* : H_r(C; ℝ) → H_r(D; ℝ)` (`HSP.realH.map`), and `G` acts on `H_r(C; ℝ)` by permuting the
basis, `(a · v)(g, k) = v(-a + g, k)` (`HSP.realH.rep`, a representation of `Multiplicative G`,
since `G` is written additively).

The real cohomology `H^r(C; ℝ)` (`HSP.realHco C r`) is the cohomology of the real cochains
`im(e_rᵀ)` with the coboundary `dᵀ`: cocycles `im(e_rᵀ) ∩ ker d_{r+1}ᵀ` modulo coboundaries
`d_rᵀ(im e_{r-1}ᵀ)`. In `Kar Free(ℚ[G])` the dual of `(n, e)` is `(n, eᵀ)` and the dual of a
morphism is its transpose, so the cochains are written with the duality. It is contravariant in
chain maps (`HSP.realHco.map`) and carries the same permutation action (`HSP.realHco.rep`).

Lean encoding: the matrices are base-changed to `ℝ` entrywise (`HSP.FreeCat.realMap`), and the
real chains are the range of the real idempotent (`HSP.realSpace`), so no tensor products are
needed. Homology is the quotient of the cycle submodule by the boundaries pulled back to it.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace HSP

open DualCat

variable {G : Type} [AddGroup G] [Fintype G]

namespace FreeCat

/-- The real matrix of `u : M ⟶ N`, acting on real vectors, `ℝ^{G × Fin M.n} → ℝ^{G × Fin N.n}`. -/
noncomputable def realMap {M N : FreeCat G} (u : M ⟶ N) :
    (G × Fin M.n → ℝ) →ₗ[ℝ] (G × Fin N.n → ℝ) :=
  ((mat u).map (Rat.cast : ℚ → ℝ)).mulVecLin

theorem realMap_apply {M N : FreeCat G} (u : M ⟶ N) (v : G × Fin M.n → ℝ) :
    realMap u v = ((mat u).map (Rat.cast : ℚ → ℝ)).mulVec v := rfl

@[simp] theorem realMap_neg {M N : FreeCat G} (u : M ⟶ N) : realMap (-u) = -realMap u := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [realMap_apply, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

@[simp] theorem realMap_add {M N : FreeCat G} (u u' : M ⟶ N) :
    realMap (u + u') = realMap u + realMap u' := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [realMap_apply, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

/-- The permutation representation `(a · v)(g, k) = v(-a + g, k)` of `G` on `ℝ^{G × Fin n}`. -/
noncomputable def permRep (n : ℕ) : Representation ℝ (Multiplicative G) (G × Fin n → ℝ) where
  toFun a := LinearMap.funLeft ℝ ℝ fun b : G × Fin n => (-Multiplicative.toAdd a + b.1, b.2)
  map_one' := by
    ext v b
    simp [LinearMap.funLeft]
  map_mul' a b := by
    ext v x
    simp [LinearMap.funLeft, neg_add_rev, add_assoc]

omit [Fintype G] in
theorem permRep_apply (n : ℕ) (a : Multiplicative G) (v : G × Fin n → ℝ) (b : G × Fin n) :
    permRep n a v b = v (-Multiplicative.toAdd a + b.1, b.2) := rfl

/-- Equivariant matrices commute with the permutation action. -/
theorem realMap_permRep {M N : FreeCat G} (u : M ⟶ N) (a : Multiplicative G)
    (v : G × Fin M.n → ℝ) : realMap u (permRep M.n a v) = permRep N.n a (realMap u v) := by
  funext x
  simp only [realMap_apply, permRep_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Fintype.sum_equiv
    ((Equiv.addLeft (-Multiplicative.toAdd a)).prodCongr (Equiv.refl _)) _ _ fun b => ?_
  simp only [Equiv.prodCongr_apply, Equiv.coe_addLeft, Equiv.coe_refl]
  congr 2
  have h := u.2 (Multiplicative.toAdd a) (-Multiplicative.toAdd a + x.1)
    (-Multiplicative.toAdd a + b.1) x.2 b.2
  simp only [add_neg_cancel_left] at h
  exact h

variable [DecidableEq G]

@[simp] theorem realMap_comp {M N P : FreeCat G} (f : M ⟶ N) (g : N ⟶ P) :
    realMap (f ≫ g) = realMap g ∘ₗ realMap f := by
  rw [realMap, realMap, realMap, mat_comp, ← Matrix.mulVecLin_mul]
  congr 1
  exact Matrix.map_mul (f := Rat.castHom ℝ)

theorem realMap_comp_apply {M N P : FreeCat G} (f : M ⟶ N) (g : N ⟶ P)
    (v : G × Fin M.n → ℝ) : realMap (f ≫ g) v = realMap g (realMap f v) := by
  rw [realMap_comp, LinearMap.comp_apply]

end FreeCat

open FreeCat

variable [DecidableEq G]

/-- The real space `im(e) ⊆ ℝ^{G × Fin n}` of an object `(n, e)` of `Kar Free(ℚ[G])`. -/
noncomputable def realSpace (P : Karoubi (FreeCat G)) : Submodule ℝ (G × Fin P.X.n → ℝ) :=
  LinearMap.range (realMap P.p)

/-- A morphism of `Kar Free(ℚ[G])` maps real spaces into real spaces. -/
theorem realMap_mem_realSpace {P Q : Karoubi (FreeCat G)} (f : P ⟶ Q) (v : G × Fin P.X.n → ℝ) :
    realMap f.f v ∈ realSpace Q := by
  refine ⟨realMap f.f v, ?_⟩
  rw [← realMap_comp_apply, Karoubi.comp_p]

/-- The permutation action preserves real spaces. -/
theorem permRep_mem_realSpace {P : Karoubi (FreeCat G)} (a : Multiplicative G)
    {v : G × Fin P.X.n → ℝ} (hv : v ∈ realSpace P) : permRep P.X.n a v ∈ realSpace P := by
  obtain ⟨w, rfl⟩ := hv
  exact ⟨permRep P.X.n a w, realMap_permRep _ _ _⟩

variable (C : ChainComplex (Karoubi (FreeCat G)) ℤ) (r : ℤ)

/-- The real cycles `im(e_r) ∩ ker d_r`. -/
noncomputable def realCycles : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  realSpace (C.X r) ⊓ LinearMap.ker (realMap (C.d r (r - 1)).f)

/-- The real boundaries `d_{r+1}(im e_{r+1})`. -/
noncomputable def realBoundaries : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  (realSpace (C.X (r + 1))).map (realMap (C.d (r + 1) r).f)

/-- The real cocycles `im(e_rᵀ) ∩ ker d_{r+1}ᵀ`. -/
noncomputable def realCocycles : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  realSpace (dual (C.X r)) ⊓ LinearMap.ker (realMap (dualHom (C.d (r + 1) r)).f)

/-- The real coboundaries `d_rᵀ(im e_{r-1}ᵀ)`. -/
noncomputable def realCoboundaries : Submodule ℝ (G × Fin (C.X r).X.n → ℝ) :=
  (realSpace (dual (C.X (r - 1)))).map (realMap (dualHom (C.d r (r - 1))).f)

/-- **Real homology** `H_r(C; ℝ)`: real cycles modulo real boundaries. -/
abbrev realH : Type :=
  realCycles C r ⧸ (realBoundaries C r).comap (realCycles C r).subtype

/-- **Real cohomology** `H^r(C; ℝ)`: real cocycles modulo real coboundaries. -/
abbrev realHco : Type :=
  realCocycles C r ⧸ (realCoboundaries C r).comap (realCocycles C r).subtype

variable {C r}

/-- The map of subquotients induced by a linear map preserving cycles and boundaries. -/
private noncomputable def subquotMap {V V' : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] {Z B : Submodule ℝ V} {Z' B' : Submodule ℝ V'} (f : V →ₗ[ℝ] V')
    (hZ : ∀ x ∈ Z, f x ∈ Z') (hB : ∀ x ∈ B, f x ∈ B') :
    (Z ⧸ B.comap Z.subtype) →ₗ[ℝ] (Z' ⧸ B'.comap Z'.subtype) :=
  Submodule.mapQ _ _ (f.restrict hZ) fun _ hx => hB _ hx

private theorem subquotMap_mk {V V' : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] {Z B : Submodule ℝ V} {Z' B' : Submodule ℝ V'} (f : V →ₗ[ℝ] V')
    (hZ : ∀ x ∈ Z, f x ∈ Z') (hB : ∀ x ∈ B, f x ∈ B') (x : Z) :
    subquotMap f hZ hB (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨f x, hZ _ x.2⟩ := rfl

/-- The representation on a subquotient by permutations preserving cycles and boundaries. -/
private noncomputable def subquotRep {n : ℕ} {Z B : Submodule ℝ (G × Fin n → ℝ)}
    (hZ : ∀ a, ∀ x ∈ Z, permRep n a x ∈ Z) (hB : ∀ a, ∀ x ∈ B, permRep n a x ∈ B) :
    Representation ℝ (Multiplicative G) (Z ⧸ B.comap Z.subtype) where
  toFun a := subquotMap (permRep n a) (hZ a) (hB a)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, subquotMap_mk, map_one,
      Module.End.one_apply]
  map_mul' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, subquotMap_mk, map_mul,
      Module.End.mul_apply]

private theorem cycles_perm (a : Multiplicative G) : ∀ x ∈ realCycles C r,
    permRep _ a x ∈ realCycles C r := fun x hx =>
  ⟨permRep_mem_realSpace a hx.1, LinearMap.mem_ker.2 (by
    rw [realMap_permRep, LinearMap.mem_ker.1 hx.2, map_zero])⟩

private theorem boundaries_perm (a : Multiplicative G) : ∀ x ∈ realBoundaries C r,
    permRep _ a x ∈ realBoundaries C r := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨permRep _ a y, permRep_mem_realSpace a hy, realMap_permRep _ _ _⟩

private theorem cocycles_perm (a : Multiplicative G) : ∀ x ∈ realCocycles C r,
    permRep _ a x ∈ realCocycles C r := fun x hx =>
  ⟨permRep_mem_realSpace (P := dual (C.X r)) a hx.1, LinearMap.mem_ker.2 (by
    rw [realMap_permRep, LinearMap.mem_ker.1 hx.2, map_zero])⟩

private theorem coboundaries_perm (a : Multiplicative G) : ∀ x ∈ realCoboundaries C r,
    permRep _ a x ∈ realCoboundaries C r := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨permRep _ a y, permRep_mem_realSpace (P := dual (C.X (r - 1))) a hy,
    realMap_permRep _ _ _⟩

/-- The action of `G` on `H_r(C; ℝ)` by permuting the basis. -/
noncomputable def realH.rep : Representation ℝ (Multiplicative G) (realH C r) :=
  subquotRep cycles_perm boundaries_perm

/-- The action of `G` on `H^r(C; ℝ)` by permuting the basis. -/
noncomputable def realHco.rep : Representation ℝ (Multiplicative G) (realHco C r) :=
  subquotRep cocycles_perm coboundaries_perm

theorem realH.rep_mk (a : Multiplicative G) (x : realCycles C r) :
    realH.rep a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨permRep _ a x, cycles_perm (C := C) (r := r) a x x.2⟩ := rfl

theorem realHco.rep_mk (a : Multiplicative G) (x : realCocycles C r) :
    realHco.rep a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨permRep _ a x, cocycles_perm (C := C) (r := r) a x x.2⟩ := rfl

variable {D : ChainComplex (Karoubi (FreeCat G)) ℤ}

private theorem map_cycles (f : C ⟶ D) : ∀ x ∈ realCycles C r,
    realMap (f.f r).f x ∈ realCycles D r := fun x hx => by
  have h := congrArg (fun h => realMap h.f x) (f.comm r (r - 1))
  simp only [Karoubi.comp_f, realMap_comp_apply] at h
  exact ⟨realMap_mem_realSpace _ _, LinearMap.mem_ker.2 (by rw [h, LinearMap.mem_ker.1 hx.2,
    map_zero])⟩

private theorem map_boundaries (f : C ⟶ D) : ∀ x ∈ realBoundaries C r,
    realMap (f.f r).f x ∈ realBoundaries D r := by
  rintro _ ⟨y, -, rfl⟩
  have h := congrArg (fun h => realMap h.f y) (f.comm (r + 1) r)
  simp only [Karoubi.comp_f, realMap_comp_apply] at h
  exact ⟨realMap (f.f (r + 1)).f y, realMap_mem_realSpace _ _, h⟩

private theorem comap_cocycles (f : C ⟶ D) : ∀ x ∈ realCocycles D r,
    realMap (dualHom (f.f r)).f x ∈ realCocycles C r := fun x hx => by
  have h := congrArg (fun h : C.X (r + 1) ⟶ D.X r => realMap (dualHom h).f x) (f.comm (r + 1) r)
  simp only [dualHom_comp, Karoubi.comp_f, realMap_comp_apply] at h
  exact ⟨realMap_mem_realSpace (dualHom (f.f r)) _,
    LinearMap.mem_ker.2 (by rw [← h, LinearMap.mem_ker.1 hx.2, map_zero])⟩

private theorem comap_coboundaries (f : C ⟶ D) : ∀ x ∈ realCoboundaries D r,
    realMap (dualHom (f.f r)).f x ∈ realCoboundaries C r := by
  rintro _ ⟨y, -, rfl⟩
  have h := congrArg (fun h : C.X r ⟶ D.X (r - 1) => realMap (dualHom h).f y) (f.comm r (r - 1))
  simp only [dualHom_comp, Karoubi.comp_f, realMap_comp_apply] at h
  exact ⟨realMap (dualHom (f.f (r - 1))).f y,
    realMap_mem_realSpace (dualHom (f.f (r - 1))) _, h.symm⟩

/-- The map `f_* : H_r(C; ℝ) → H_r(D; ℝ)` induced by a chain map. -/
noncomputable def realH.map (f : C ⟶ D) : realH C r →ₗ[ℝ] realH D r :=
  subquotMap _ (map_cycles f) (map_boundaries f)

/-- The map `f^* : H^r(D; ℝ) → H^r(C; ℝ)` induced by a chain map, by the transposed matrices. -/
noncomputable def realHco.map (f : C ⟶ D) : realHco D r →ₗ[ℝ] realHco C r :=
  subquotMap _ (comap_cocycles f) (comap_coboundaries f)

theorem realHco.map_mk (f : C ⟶ D) (x : realCocycles D r) :
    realHco.map f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨realMap (dualHom (f.f r)).f x, comap_cocycles (r := r) f x x.2⟩ := rfl

end HSP

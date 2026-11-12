import Mathlib
import HilbertSmithPaper.Categories.Asymptotic.EventuallyZeroSubcategory
import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration

/-!
# Point filtration

`𝒮_𝐆 ⊂ 𝒫_𝐆` is an involution-invariant Karoubi filtration. The chosen decompositions of
`M = (n_i)` are the truncations `p_N` (`N ∈ ℕ`): the identity in the coordinates `i < N` and zero
in the coordinates `i ≥ N`. `p_N` splits through `M_{<N}` (`n_i` for `i < N`, the zero object
elsewhere) and `1 - p_N` through `M_{≥N}` (`n_i` for `i ≥ N`, the zero object elsewhere); the
inclusions and projections are identity matrices in the coordinates where they are defined.

Lean encoding. `HSP.SCat.isDualAdditive` records step 1 (a full additive subcategory closed under
duality: the zero sequence, the coordinatewise sum `(n_i + m_i)`, and `M^* = M`). The truncation
objects and maps are written for a decidable set `S` of indices (`S = {i < N}` and its complement),
with the object `⟨if i ∈ S then n_i else 0⟩` at `i`, so that no transport is needed outside `S`.
The filtration is `HSP.SCat.karoubiFiltration`, with `D M` the range of `N ↦ p_N`.
-/

open CategoryTheory CategoryTheory.Limits

namespace HSP

variable {p : ℕ} {G : GroupSeq p}

/-- Step 1: `𝒮_𝐆` is a full additive subcategory closed under the duality `M^* = M`. -/
instance SCat.isDualAdditive : IsDualAdditive (SCat G) where
  exists_zero := ⟨fun _ => ⟨0⟩, by simp [SCat, PCat.coord], PCat.isZero_zero⟩
  exists_biprod {V W} hV hW := by
    refine ⟨PCat.binaryBicone V W,
      ⟨isBinaryBilimitOfTotal _ (PCat.binaryBicone_total V W)⟩, ?_⟩
    refine (hV.union hW).subset fun i hi => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hi (show (V.coord i).n + (W.coord i).n = 0 by rw [h.1, h.2])
  dual_mem h := h

namespace PCat

variable (M : PCat G) (S : ℕ → Prop) [DecidablePred S]

/-- The truncated object: `n_i` for `i ∈ S`, the zero object `0` elsewhere. -/
private def truncObj : PCat G := fun i => ⟨if S i then (M.coord i).n else 0⟩

variable {M S}

private theorem truncObj_coord_of {i : ℕ} (h : S i) : (truncObj M S).coord i = M.coord i := by
  show (⟨if S i then (M.coord i).n else 0⟩ : FreeCat (G.G i)) = M.coord i
  rw [ite_eq_left h]

private theorem truncObj_isZero_of {i : ℕ} (h : ¬S i) : IsZero ((truncObj M S).coord i) :=
  FreeCat.isZero_of_n_eq_zero _
    (by show (if S i then (M.coord i).n else 0) = 0; rw [ite_eq_right h])

variable (M S)

/-- The inclusion `M_S → M`: identity matrices on `S`. -/
private def truncInc : truncObj M S ⟶ M :=
  fun i => (if h : S i then eqToHom (truncObj_coord_of h) else 0 :
    (truncObj M S).coord i ⟶ M.coord i)

/-- The projection `M → M_S`: identity matrices on `S`. -/
private def truncPro : M ⟶ truncObj M S :=
  fun i => (if h : S i then eqToHom (truncObj_coord_of h).symm else 0 :
    M.coord i ⟶ (truncObj M S).coord i)

/-- The truncation `p_S : M → M`: the identity on `S` and zero elsewhere. -/
private def trunc : M ⟶ M := fun i => (if S i then 𝟙 (M.coord i) else 0 : M.coord i ⟶ M.coord i)

private theorem homCoord_trunc (i : ℕ) :
    homCoord (trunc M S) i = if S i then 𝟙 (M.coord i) else 0 := rfl

private theorem homCoord_truncInc (i : ℕ) : homCoord (truncInc M S) i =
    (if h : S i then eqToHom (truncObj_coord_of h) else 0 :
      (truncObj M S).coord i ⟶ M.coord i) := rfl

private theorem homCoord_truncPro (i : ℕ) : homCoord (truncPro M S) i =
    (if h : S i then eqToHom (truncObj_coord_of h).symm else 0 :
      M.coord i ⟶ (truncObj M S).coord i) := rfl

private theorem truncInc_truncPro : truncInc M S ≫ truncPro M S = 𝟙 (truncObj M S) := by
  refine hom_ext fun i => ?_
  by_cases h : S i
  · rw [homCoord_comp, homCoord_truncInc, homCoord_truncPro, dite_eq_left h, dite_eq_left h,
      eqToHom_trans, eqToHom_refl]; rfl
  · exact (truncObj_isZero_of h).eq_of_src _ _

private theorem truncPro_truncInc : truncPro M S ≫ truncInc M S = trunc M S := by
  refine hom_ext fun i => ?_
  rw [homCoord_comp, homCoord_truncInc, homCoord_truncPro, homCoord_trunc]
  by_cases h : S i
  · rw [dite_eq_left h, dite_eq_left h, ite_eq_left h, eqToHom_trans, eqToHom_refl]
  · rw [dite_eq_right h, dite_eq_right h, ite_eq_right h, Limits.zero_comp]

private theorem trunc_not : trunc M (fun i => ¬S i) = 𝟙 M - trunc M S := by
  refine hom_ext fun i => ?_
  rw [homCoord_sub, homCoord_trunc, homCoord_trunc, homCoord_id]
  by_cases h : S i
  · rw [ite_eq_right (not_not.2 h), ite_eq_left h, sub_self]
  · rw [ite_eq_left h, ite_eq_right h, sub_zero]

private theorem trunc_comp_trunc (S' : ℕ → Prop) [DecidablePred S'] :
    trunc M S ≫ trunc M S' = trunc M (fun i => S i ∧ S' i) := by
  refine hom_ext fun i => ?_
  rw [homCoord_comp, homCoord_trunc, homCoord_trunc, homCoord_trunc]
  by_cases h : S i <;> by_cases h' : S' i <;> simp [h, h']

private theorem trunc_congr {S' : ℕ → Prop} [DecidablePred S'] (h : ∀ i, S i ↔ S' i) :
    trunc M S = trunc M S' := by
  refine hom_ext fun i => ?_
  rw [homCoord_trunc, homCoord_trunc]
  by_cases hi : S i
  · rw [ite_eq_left hi, ite_eq_left ((h i).1 hi)]
  · rw [ite_eq_right hi, ite_eq_right (fun h' => hi ((h i).2 h'))]

private theorem dualHom_trunc : DualCat.dualHom (trunc M S) = trunc M S := by
  refine hom_ext fun i => FreeCat.hom_ext ?_
  rw [homCoord_dualHom, FreeCat.mat_dualHom, homCoord_trunc]
  by_cases h : S i
  · rw [ite_eq_left h, FreeCat.mat_id, Matrix.transpose_one]
  · rw [ite_eq_right h, FreeCat.mat_zero, Matrix.transpose_zero]

end PCat

open PCat

/-- If `V` is the zero object in all coordinates `i ≥ N`, every map out of `V` vanishes there. -/
private theorem exists_bound {V : PCat G} (hV : SCat G V) :
    ∃ N : ℕ, ∀ i, N ≤ i → (V.coord i).n = 0 := by
  obtain ⟨N, hN⟩ := hV.bddAbove
  refine ⟨N + 1, fun i hi => ?_⟩
  by_contra h
  have := hN h
  omega

/-- The point filtration: `𝒮_𝐆 ⊂ 𝒫_𝐆` is an involution-invariant Karoubi filtration, with the
truncations `p_N` (identity in the coordinates `i < N`, zero elsewhere) as chosen
decompositions. -/
noncomputable def SCat.karoubiFiltration : KaroubiFiltration (SCat G) where
  D M := Set.range fun N : ℕ => trunc M (fun i => i < N)
  idem := by
    rintro M _ ⟨N, rfl⟩
    rw [trunc_comp_trunc]
    exact trunc_congr M _ fun i => and_self_iff
  split := by
    rintro M _ ⟨N, rfl⟩
    refine ⟨truncObj M (fun i => i < N), ?_, truncInc M _, truncPro M _,
      truncInc_truncPro M _, truncPro_truncInc M _⟩
    refine (Set.finite_lt_nat N).subset fun i hi => ?_
    by_contra h
    exact hi (by show (if i < N then _ else 0) = 0; exact ite_eq_right h)
  split_compl := by
    rintro M _ ⟨N, rfl⟩
    exact ⟨truncObj M (fun i => ¬i < N), truncInc M _, truncPro M _, truncInc_truncPro M _,
      (truncPro_truncInc M _).trans (trunc_not M _)⟩
  nonempty M := ⟨_, 0, rfl⟩
  directed := by
    rintro M _ _ ⟨N, rfl⟩ ⟨N', rfl⟩
    refine ⟨_, ⟨max N N', rfl⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [trunc_comp_trunc] <;>
      exact trunc_congr M _ fun i => by omega
  factor_left := by
    intro V M g hV
    obtain ⟨N, hN⟩ := exists_bound hV
    refine ⟨_, ⟨N, rfl⟩, hom_ext fun i => ?_⟩
    rw [homCoord_comp, homCoord_trunc]
    by_cases h : i < N
    · rw [ite_eq_left h, Category.comp_id]
    · rw [ite_eq_right h, Limits.comp_zero]
      exact ((FreeCat.isZero_of_n_eq_zero _ (hN i (by omega))).eq_of_src _ _).symm
  factor_right := by
    intro M V g hV
    obtain ⟨N, hN⟩ := exists_bound hV
    refine ⟨_, ⟨N, rfl⟩, hom_ext fun i => ?_⟩
    rw [homCoord_comp, homCoord_trunc]
    by_cases h : i < N
    · rw [ite_eq_left h, Category.id_comp]
    · rw [ite_eq_right h, Limits.zero_comp]
      exact ((FreeCat.isZero_of_n_eq_zero _ (hN i (by omega))).eq_of_tgt _ _).symm
  dual_mem_iff := by
    intro M q
    constructor
    · rintro ⟨N, rfl⟩
      exact ⟨N, (dualHom_trunc M _).symm⟩
    · rintro ⟨N, hN⟩
      refine ⟨N, ?_⟩
      have h := DualCat.dualHom_dualHom q
      rw [← hN, dualHom_trunc] at h
      have h' : q = trunc M (fun i => i < N) := by
        have h2 := h.symm
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h2
        exact h2
      exact h'.symm

end HSP

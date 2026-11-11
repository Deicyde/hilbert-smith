import HilbertSmithPaper.LTheory.Base.Categories.KaroubiFiltration
import HilbertSmithPaper.LTheory.Bounded.Categories.BoundedDuality

/-!
# Bounded Karoubi filtrations

For an involution-invariant Karoubi filtration of `A` by `U`, `C_ℤ(U) ⊂ C_ℤ(A)` (`Bounded.sub U`:
the objects with every `M_n` in `U`) is an involution-invariant Karoubi filtration whose chosen
decompositions of `M` are the diagonal idempotents `p = diag (p_n)` (propagation `0`) with
`p_n ∈ D(M_n)` for every `n`.

`C_ℤ(U)` is a full additive subcategory closed under duality (`Bounded.isDualAdditive_sub`, an
instance): the constant family at a zero object of `U` is a zero object, sums are assembled from
degreewise bilimit bicones in `U`, and `(M^*)_n = (M_n)^*`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HSP

open DualCat

universe v u

namespace Bounded

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℚ A] [HasFiniteBiproducts A]
  [DualCat A]

/-- `C_ℤ(U)`: the objects of `C_ℤ(A)` with every `M_n` in `U`. -/
def sub (U : ObjectProperty A) : ObjectProperty (Bounded A) := fun M => ∀ n, U (M.X n)

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma diag_id_eq (M : Bounded A) : (diag fun n => 𝟙 (M.X n)) = 𝟙 M := rfl

omit [Linear ℚ A] [HasFiniteBiproducts A] [DualCat A] in
private lemma bilimit_total {X Y : A} {c : BinaryBicone X Y} (hc : c.IsBilimit) :
    c.fst ≫ c.inl + c.snd ≫ c.inr = 𝟙 c.pt := by
  refine BinaryFan.IsLimit.hom_ext hc.isLimit ?_ ?_ <;> simp

instance isDualAdditive_sub (U : ObjectProperty A) [IsDualAdditive U] :
    IsDualAdditive (sub U) where
  exists_zero := by
    obtain ⟨Z, hZ, hZ0⟩ := IsDualAdditive.exists_zero (U := U)
    refine ⟨⟨fun _ => Z⟩, fun _ => hZ, ?_⟩
    rw [IsZero.iff_id_eq_zero, ← diag_id_eq]
    rw [show (fun _ : ℤ => 𝟙 Z) = fun _ => 0 from funext fun _ => hZ0.eq_of_src _ _]
    exact diag_zero
  exists_biprod {V W} hV hW := by
    choose c hc hcU using fun n => IsDualAdditive.exists_biprod (hV n) (hW n)
    let P : Bounded A := ⟨fun n => (c n).pt⟩
    let b : BinaryBicone V W :=
      { pt := P
        fst := diag (M := P) (N := V) fun n => (c n).fst
        snd := diag (M := P) (N := W) fun n => (c n).snd
        inl := diag (M := V) (N := P) fun n => (c n).inl
        inr := diag (M := W) (N := P) fun n => (c n).inr
        inl_fst := by rw [diag_comp_diag]; simp only [BinaryBicone.inl_fst]; rfl
        inl_snd := by rw [diag_comp_diag]; simp only [BinaryBicone.inl_snd]; exact diag_zero
        inr_fst := by rw [diag_comp_diag]; simp only [BinaryBicone.inr_fst]; exact diag_zero
        inr_snd := by rw [diag_comp_diag]; simp only [BinaryBicone.inr_snd]; rfl }
    refine ⟨b, ⟨isBinaryBilimitOfTotal b ?_⟩, fun n => hcU n⟩
    change (diag (M := P) (N := V) fun n => (c n).fst) ≫
        (diag (M := V) (N := P) fun n => (c n).inl) +
      (diag (M := P) (N := W) fun n => (c n).snd) ≫
        (diag (M := W) (N := P) fun n => (c n).inr) = 𝟙 P
    rw [diag_comp_diag, diag_comp_diag]
    refine hom_ext fun m n => ?_
    rw [add_apply, diag_apply, diag_apply, ← diag_id_eq, diag_apply]
    by_cases h : m = n
    · subst h
      simp only [diagF_self]
      exact bilimit_total (hc m).some
    · simp only [diagF_ne _ h, add_zero]
  dual_mem hV n := IsDualAdditive.dual_mem (hV n)

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma diag_sub' {M N : Bounded A} (a b : ∀ n, M.X n ⟶ N.X n) :
    (diag fun n => a n - b n) = diag a - diag b := hom_ext fun m n => by
  change diagF (fun n => a n - b n) m n = diagF a m n - diagF b m n
  by_cases h : m = n
  · subst h; simp only [diagF_self]
  · simp only [diagF_ne _ h, sub_zero]

omit [HasFiniteBiproducts A] [DualCat A] in
private lemma diag_congr' {M N : Bounded A} {a b : ∀ n, M.X n ⟶ N.X n} (h : ∀ n, a n = b n) :
    diag a = diag b := congrArg diag (funext h)

private lemma dualHom_injective_zero {X Y : A} {x : X ⟶ Y} (h : dualHom x = 0) : x = 0 := by
  have h2 := dualHom_dualHom x
  rw [h, dualHom_zero] at h2
  have h3 := congrArg (fun q => eqToHom (dual_dual X).symm ≫ q ≫ eqToHom (dual_dual Y)) h2
  simpa using h3.symm

private lemma dualHom_diag {M : Bounded A} (d : ∀ n, M.X n ⟶ M.X n) :
    dualHom (diag d) = diag (M := dual M) (N := dual M) (fun n => dualHom (d n)) :=
  hom_ext fun a b => by
    rw [dualHom_apply]
    change dualHom (diagF d b a) = diagF (M := dual M) (N := dual M) (fun n => dualHom (d n)) a b
    by_cases h : a = b
    · subst h; rw [diagF_self, diagF_self]
    · rw [diagF_ne _ (Ne.symm h), diagF_ne _ h, dualHom_zero]

variable {U : ObjectProperty A} [IsDualAdditive U]

private lemma exists_factor_left_finset (F : KaroubiFiltration U) {X : A} {ι : Type*}
    (s : Finset ι) (V : ι → A) (hV : ∀ i, U (V i)) (g : ∀ i, V i ⟶ X) :
    ∃ p ∈ F.D X, ∀ i ∈ s, g i ≫ p = g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := F.nonempty X
    exact ⟨p, hp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨p, hp, hps⟩ := ih
    obtain ⟨q, hq, hqa⟩ := F.factor_left (g a) (hV a)
    obtain ⟨p'', hp'', ⟨h1, -⟩, ⟨h2, -⟩⟩ := F.directed hp hq
    refine ⟨p'', hp'', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← hqa, Category.assoc, h2]
    · rw [← hps i hi, Category.assoc, h1]

private lemma exists_factor_right_finset (F : KaroubiFiltration U) {X : A} {ι : Type*}
    (s : Finset ι) (V : ι → A) (hV : ∀ i, U (V i)) (h : ∀ i, X ⟶ V i) :
    ∃ p ∈ F.D X, ∀ i ∈ s, p ≫ h i = h i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := F.nonempty X
    exact ⟨p, hp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨p, hp, hps⟩ := ih
    obtain ⟨q, hq, hqa⟩ := F.factor_right (h a) (hV a)
    obtain ⟨p'', hp'', ⟨-, h1⟩, ⟨-, h2⟩⟩ := F.directed hp hq
    refine ⟨p'', hp'', fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← hqa, ← Category.assoc, h2]
    · rw [← hps i hi, ← Category.assoc, h1]

/-- **Bounded Karoubi filtrations.** For an involution-invariant Karoubi filtration `F` of `A` by
`U`, `C_ℤ(U) ⊂ C_ℤ(A)` is an involution-invariant Karoubi filtration whose chosen decompositions
of `M` are the diagonal idempotents `diag (p_n)` with `p_n ∈ D(M_n)` for every `n`. -/
def karoubiFiltration (F : KaroubiFiltration U) : KaroubiFiltration (sub U) where
  D M := {p | ∃ d : ∀ n, M.X n ⟶ M.X n, p = diag d ∧ ∀ n, d n ∈ F.D (M.X n)}
  idem := by
    rintro M _ ⟨d, rfl, hd⟩
    rw [diag_comp_diag]
    exact diag_congr' fun n => F.idem (hd n)
  split := by
    rintro M _ ⟨d, rfl, hd⟩
    choose E hE i r hir hri using fun n => F.split (hd n)
    refine ⟨⟨E⟩, hE, diag (M := ⟨E⟩) (N := M) i, diag (M := M) (N := ⟨E⟩) r, ?_, ?_⟩
    · rw [diag_comp_diag, ← diag_id_eq]; exact diag_congr' hir
    · rw [diag_comp_diag]; exact diag_congr' hri
  split_compl := by
    rintro M _ ⟨d, rfl, hd⟩
    choose M' i r hir hri using fun n => F.split_compl (hd n)
    refine ⟨⟨M'⟩, diag (M := ⟨M'⟩) (N := M) i, diag (M := M) (N := ⟨M'⟩) r, ?_, ?_⟩
    · rw [diag_comp_diag, ← diag_id_eq]; exact diag_congr' hir
    · rw [diag_comp_diag, ← diag_id_eq, ← diag_sub']; exact diag_congr' hri
  nonempty := by
    intro M
    choose p hp using fun n => F.nonempty (M.X n)
    exact ⟨diag p, p, rfl, hp⟩
  directed := by
    rintro M _ _ ⟨d, rfl, hd⟩ ⟨d', rfl, hd'⟩
    choose e he h1 h2 using fun n => F.directed (hd n) (hd' n)
    refine ⟨diag e, ⟨e, rfl, he⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rw [diag_comp_diag] <;>
      exact diag_congr' fun n => by simp [h1 n, h2 n]
  factor_left := by
    intro V M g hV
    obtain ⟨r, hr⟩ := g.2
    choose p hp hpg using fun l : ℤ => exists_factor_left_finset F (Finset.Icc (l - r) (l + r))
      V.X hV (fun n => g.1 l n)
    refine ⟨diag p, ⟨p, rfl, hp⟩, hom_ext fun l n => ?_⟩
    change compF g.1 (diagF p) l n = g.1 l n
    rw [compF_diagF]
    by_cases hn : n ∈ Finset.Icc (l - r) (l + r)
    · exact hpg l n hn
    · rw [hr l n (by rw [Finset.mem_Icc] at hn; rw [lt_abs]; omega), zero_comp]
  factor_right := by
    intro M V h hV
    obtain ⟨r, hr⟩ := h.2
    choose p hp hph using fun n : ℤ => exists_factor_right_finset F (Finset.Icc (n - r) (n + r))
      V.X hV (fun l => h.1 l n)
    refine ⟨diag p, ⟨p, rfl, hp⟩, hom_ext fun l n => ?_⟩
    change compF (diagF p) h.1 l n = h.1 l n
    rw [diagF_compF]
    by_cases hl : l ∈ Finset.Icc (n - r) (n + r)
    · exact hph n l hl
    · rw [hr l n (by rw [Finset.mem_Icc] at hl; rw [lt_abs]; omega), comp_zero]
  dual_mem_iff := by
    intro M p
    constructor
    · rintro ⟨d, rfl, hd⟩
      exact ⟨fun n => dualHom (d n), dualHom_diag d, fun n => (F.dual_mem_iff (d n)).1 (hd n)⟩
    · rintro ⟨e, he, hed⟩
      have hoff : ∀ m n, m ≠ n → p.1 m n = 0 := fun m n hmn => by
        apply dualHom_injective_zero
        have := congrArg (fun q => q.1 n m) he
        simp only [dualHom_apply] at this
        rw [this]
        exact diagF_ne _ (Ne.symm hmn)
      have hdiag : ∀ n, dualHom (p.1 n n) = e n := fun n => by
        have := congrArg (fun q => q.1 n n) he
        simp only [dualHom_apply] at this
        rw [this]
        exact diagF_self _ n
      refine ⟨fun n => p.1 n n, hom_ext fun m n => ?_, fun n => ?_⟩
      · change p.1 m n = diagF (fun n => p.1 n n) m n
        by_cases h : m = n
        · subst h; rw [diagF_self]
        · rw [diagF_ne _ h, hoff m n h]
      · rw [F.dual_mem_iff, hdiag]
        exact hed n

end Bounded

end HSP

end

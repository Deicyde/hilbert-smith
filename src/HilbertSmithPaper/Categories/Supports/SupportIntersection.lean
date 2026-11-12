import HilbertSmithPaper.Categories.Supports.SupportSubcategory

/-!
# Support intersection

For a compact metric space `X` and closed `A, B ⊆ X`, an object of `𝒜_𝐆(X)` is `A`- and
`B`-supported if and only if it is `(A ∩ B)`-supported (`HSP.supp_inter`). The key step
(`HSP.exists_thickening_inter_subset`): for every `ε > 0` some `δ > 0` has
`N_δ(A) ∩ N_δ(B) ⊆ N_ε(A ∩ B)`, since the compact sets
`N̄_{1/(m+1)}(A) ∩ N̄_{1/(m+1)}(B) ∖ N_ε(A ∩ B)` decrease and have empty intersection.
Invariance is not used.
-/

open Filter Metric

namespace HSP

variable {X : Type*} [MetricSpace X]

/-- For compact `X` and closed `A, B`, every `ε`-thickening of `A ∩ B` contains the intersection of
some `δ`-thickenings of `A` and of `B`. -/
private theorem exists_thickening_inter_subset [CompactSpace X] {A B : Set X} (hA : IsClosed A)
    (hB : IsClosed B) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, thickening δ A ∩ thickening δ B ⊆ thickening ε (A ∩ B) := by
  by_contra h
  simp only [not_exists, not_and, Set.not_subset] at h
  let K : ℕ → Set X := fun m =>
    (cthickening (1 / ((m : ℝ) + 1)) A ∩ cthickening (1 / ((m : ℝ) + 1)) B) \
      thickening ε (A ∩ B)
  have hKc : ∀ m, IsClosed (K m) := fun m =>
    (isClosed_cthickening.inter isClosed_cthickening).sdiff isOpen_thickening
  have hKne : ∀ m, (K m).Nonempty := fun m => by
    obtain ⟨x, ⟨hxA, hxB⟩, hx⟩ := h (1 / ((m : ℝ) + 1)) (by positivity)
    exact ⟨x, ⟨thickening_subset_cthickening _ _ hxA, thickening_subset_cthickening _ _ hxB⟩,
      hx⟩
  have hanti : Antitone K := fun m n hmn x hx => by
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    exact ⟨⟨cthickening_mono hle _ hx.1.1, cthickening_mono hle _ hx.1.2⟩, hx.2⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K
    hanti.directed_ge hKne (fun m => (hKc m).isCompact) hKc
  rw [Set.mem_iInter] at hx
  have hmem : ∀ {C : Set X}, IsClosed C →
      (∀ m : ℕ, x ∈ cthickening (1 / ((m : ℝ) + 1)) C) → x ∈ C := by
    intro C hC hm
    rw [← hC.closure_eq, closure_eq_iInter_cthickening, Set.mem_iInter₂]
    intro δ hδ
    obtain ⟨m, hm'⟩ := exists_nat_one_div_lt hδ
    exact cthickening_mono hm'.le _ (hm m)
  have hxA : x ∈ A := hmem hA fun m => (hx m).1.1
  have hxB : x ∈ B := hmem hB fun m => (hx m).1.2
  exact (hx 0).2 (self_subset_thickening hε _ ⟨hxA, hxB⟩)

variable {p : ℕ} {G : GroupSeq p} [AddAction (ZMod p) X]

/-- **Support intersection.** For compact `X` and closed `A, B`, an object lies in `𝒜_A` and in
`𝒜_B` if and only if it lies in `𝒜_{A ∩ B}`. -/
theorem supp_inter [CompactSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (P : AsymCat G X) : supp A P ∧ supp B P ↔ supp (A ∩ B) P := by
  constructor
  · rintro ⟨hPA, hPB⟩ ε hε
    obtain ⟨δ, hδ, hsub⟩ := exists_thickening_inter_subset hA hB hε
    filter_upwards [hPA δ hδ, hPB δ hδ] with i h1 h2 k
    exact hsub ⟨h1 k, h2 k⟩
  · intro h
    refine ⟨fun ε hε => (h ε hε).mono fun i hi k => ?_, fun ε hε => (h ε hε).mono fun i hi k => ?_⟩
    · exact thickening_subset_of_subset ε Set.inter_subset_left (hi k)
    · exact thickening_subset_of_subset ε Set.inter_subset_right (hi k)

end HSP

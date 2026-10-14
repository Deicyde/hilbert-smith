import Mathlib

namespace HilbertSmith

/-- The kernel of `f` is annihilated by `q`: every element killed by `f`
is killed by scalar multiplication by `q`. -/
def kerAnnihilated {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (q : ℕ) : Prop :=
  ∀ x, f x = 0 → q • x = 0

/-- The cokernel of `f` is annihilated by `q`: every target element
times `q` lies in the image of `f`. -/
def cokerAnnihilated {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (q : ℕ) : Prop :=
  ∀ y, ∃ x, f x = q • y

/-- Triple scalar multiplication by `q` equals multiplication by `q ^ 3`. -/
theorem nsmul_pow_three {M : Type*} [AddCommGroup M] (q : ℕ) (x : M) :
    q • (q • (q • x)) = (q ^ 3) • x := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  ring

/-- Five-term chase: in a commutative diagram of exact rows, if the
kernels and cokernels of the outer four vertical maps are annihilated
by `q`, then those of the middle map are annihilated by `q ^ 3`. -/
theorem fiveTermChase {A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 : Type*}
    [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup A3]
    [AddCommGroup A4] [AddCommGroup A5]
    [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3]
    [AddCommGroup B4] [AddCommGroup B5]
    (a1 : A1 →+ A2) (a2 : A2 →+ A3) (a3 : A3 →+ A4) (a4 : A4 →+ A5)
    (b1 : B1 →+ B2) (b2 : B2 →+ B3) (b3 : B3 →+ B4) (b4 : B4 →+ B5)
    (f1 : A1 →+ B1) (f2 : A2 →+ B2) (f3 : A3 →+ B3) (f4 : A4 →+ B4)
    (f5 : A5 →+ B5)
    (hexA2 : Function.Exact (⇑a1) (⇑a2))
    (hexA3 : Function.Exact (⇑a2) (⇑a3))
    (hexA4 : Function.Exact (⇑a3) (⇑a4))
    (hexB2 : Function.Exact (⇑b1) (⇑b2))
    (hexB3 : Function.Exact (⇑b2) (⇑b3))
    (hexB4 : Function.Exact (⇑b3) (⇑b4))
    (hcomm1 : ∀ x, f2 (a1 x) = b1 (f1 x))
    (hcomm2 : ∀ x, f3 (a2 x) = b2 (f2 x))
    (hcomm3 : ∀ x, f4 (a3 x) = b3 (f3 x))
    (hcomm4 : ∀ x, f5 (a4 x) = b4 (f4 x))
    (q : ℕ)
    (hker1 : kerAnnihilated f1 q) (hcoker1 : cokerAnnihilated f1 q)
    (hker2 : kerAnnihilated f2 q) (hcoker2 : cokerAnnihilated f2 q)
    (hker4 : kerAnnihilated f4 q) (hcoker4 : cokerAnnihilated f4 q)
    (hker5 : kerAnnihilated f5 q) (hcoker5 : cokerAnnihilated f5 q) :
    kerAnnihilated f3 (q ^ 3) ∧ cokerAnnihilated f3 (q ^ 3) := by
  constructor
  · -- Kernel part: `q ^ 3` kills every element killed by `f3`.
    intro x hx
    have h1 : a3 (q • x) = 0 := by
      rw [map_nsmul]
      refine hker4 _ ?_
      rw [hcomm3, hx, map_zero]
    obtain ⟨v, hv⟩ := (hexA3 _).mp h1
    have h2 : b2 (f2 v) = 0 := by
      have : f3 (a2 v) = 0 := by rw [hv, map_nsmul, hx, nsmul_zero]
      rwa [hcomm2] at this
    obtain ⟨w, hw⟩ := (hexB2 _).mp h2
    obtain ⟨z, hz⟩ := hcoker1 w
    have hmem : f2 (q • v - a1 z) = 0 := by
      rw [map_sub, map_nsmul, hcomm1, hz, map_nsmul, hw, sub_self]
    have hann := hker2 _ hmem
    have hdone : q • (q • (q • x)) = 0 := by
      have h := congrArg (⇑a2) hann
      rwa [map_nsmul, map_sub, map_nsmul, hv,
        hexA2.apply_apply_eq_zero, sub_zero, map_zero] at h
    rwa [nsmul_pow_three] at hdone
  · -- Cokernel part: every target element times `q ^ 3` is hit.
    intro y
    obtain ⟨v, hv⟩ := hcoker4 (b3 y)
    have h1 : f5 (a4 v) = 0 := by
      rw [hcomm4, hv, map_nsmul, hexB4.apply_apply_eq_zero, nsmul_zero]
    have hann := hker5 _ h1
    have h2 : a4 (q • v) = 0 := by
      rw [map_nsmul]
      exact hann
    obtain ⟨w, hw⟩ := (hexA4 _).mp h2
    have h3 : b3 (q • (q • y) - f3 w) = 0 := by
      rw [map_sub, map_nsmul, map_nsmul, ← hcomm3, hw, map_nsmul, hv,
        sub_self]
    obtain ⟨z, hz⟩ := (hexB3 _).mp h3
    obtain ⟨t, ht⟩ := hcoker2 z
    have hT : q • (q • y) = b2 z + f3 w := by
      rw [hz]
      exact (sub_add_cancel _ _).symm
    refine ⟨q • w + a2 t, ?_⟩
    have hfin : f3 (q • w + a2 t) = q • (q • (q • y)) := by
      rw [map_add, map_nsmul, hcomm2, ht, map_nsmul, add_comm (q • f3 w),
        ← nsmul_add, hT]
    rw [hfin, nsmul_pow_three]

/-- Square chase: if both horizontal kernels and cokernels are
annihilated by `2` and those of `f` by `q`, then the kernel of `g`
is annihilated by `4 * q` and its cokernel even by `2 * q`. -/
theorem squareChase {A A' B B' : Type*} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    (i : A →+ A') (j : B →+ B') (f : A →+ B) (g : A' →+ B')
    (hcomm : ∀ x, g (i x) = j (f x))
    (q : ℕ)
    (hkerI : kerAnnihilated i 2) (hcokerI : cokerAnnihilated i 2)
    (hkerJ : kerAnnihilated j 2) (hcokerJ : cokerAnnihilated j 2)
    (hkerF : kerAnnihilated f q) (hcokerF : cokerAnnihilated f q) :
    kerAnnihilated g (4 * q) ∧ cokerAnnihilated g (2 * q) := by
  constructor
  · -- Kernel part.
    intro x' hx
    obtain ⟨x, hxx⟩ := hcokerI x'
    have h1 : j (f x) = 0 := by
      rw [← hcomm, hxx, map_nsmul, hx, nsmul_zero]
    have hannJ := hkerJ _ h1
    have h2 : f (2 • x) = 0 := by
      rw [map_nsmul]
      exact hannJ
    have hannF := hkerF _ h2
    have hdone : q • (2 • (2 • x')) = 0 := by
      have h := congrArg (⇑i) hannF
      rwa [map_nsmul, map_nsmul, hxx, map_zero] at h
    have h46 : q • (2 • (2 • x')) = (4 * q) • x' := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      ring
    rwa [h46] at hdone
  · -- Cokernel part.
    intro y'
    obtain ⟨y, hy⟩ := hcokerJ y'
    obtain ⟨x, hx⟩ := hcokerF y
    refine ⟨i x, ?_⟩
    have h26 : q • (2 • y') = (2 * q) • y' := by
      rw [← mul_smul, mul_comm]
    rw [hcomm, hx, map_nsmul, hy, h26]

end HilbertSmith

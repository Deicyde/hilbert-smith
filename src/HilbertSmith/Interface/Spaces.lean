import HilbertSmith.CollapseCompactification
import HilbertSmith.HomotopyExtension

/-!
# Spaces, actions and tests for OpenAI's route

The point-set data that §§5–6 of OpenAI's preprint work with, stated concretely.

* `IsGood`, `HasGoodBasisAt`: nonempty contractible open sets (the hypothesis of Proposition 4.9)
  and points with a basis of them (the standing hypothesis on `b_t` in §6).
* `RatEq`: equality after tensoring with `ℚ`.
* `DegreeMaps`, `DegreeMaps.comp`: fixed self-maps `D k` of `S^d`, meant to be the based cellular
  degree-`k` maps of the telescope (5.3), and their composites `D_s`.
* `ClosePair d`: the close-pair test `C_d` of (6.11).
* `Λ`, `ζ`, `χ`, `IsCyclicPartition`: the `p`-power roots of unity, the characters of `ℤ_[p]` and
  the cyclic partitions (6.12).
* `LocalAction p k`: a jointly continuous action of `ℤ_[p]` on an open subset `W` of a
  `k`-dimensional real normed space. Its one-point compactification `W⁺` with the action
  fixing `∞` (Lemma 5.2), the orbit space `Y = W⁺/ℤ_[p]` with orbit map `q`, the point
  `y∞ = q(∞)`, and the collapse `c : S^k → W⁺` of Lemma 5.2 are definitions.
* `LocalAction.restrict`: the action of the open subgroup `p^j ℤ_[p]`, identified with `ℤ_[p]`
  (the replacements of `G` by an open subgroup in Proposition 5.1 and Lemma 5.3).
* `LocalAction.stabilize`: the action on `W × ℝ^m`, trivial on the second factor (§5, after
  Proposition 5.1).
* `SheetMultiplier`: the output of Lemma 5.6.

The sphere `S^d` is Deicyde's `HilbertSmith.Sphere d`, the unit vectors of `ℝ^{d+1}`, so that
`HilbertSmith.homotopyExtension` (Lemma 5.7) applies.
-/

namespace HilbertSmith.Interface

open Topology Set OnePoint

noncomputable section

/-! ### Good neighbourhoods and rational equality -/

/-- A **good** set: nonempty, open and contractible, as in Proposition 4.9. -/
structure IsGood {X : Type*} [TopologicalSpace X] (U : Set X) : Prop where
  /-- It is open. -/
  isOpen : IsOpen U
  /-- It is nonempty. -/
  nonempty : U.Nonempty
  /-- It is contractible. -/
  contractible : ContractibleSpace U

/-- `b` has a basis of good neighbourhoods, the standing hypothesis on `b_t = t(y∞)` in §6
(06:101-107) and in Propositions 6.4 and 6.5. -/
def HasGoodBasisAt {X : Type*} [TopologicalSpace X] (b : X) : Prop :=
  ∀ N ∈ 𝓝 b, ∃ U ⊆ N, b ∈ U ∧ IsGood U

/-- `x ⊗ 1 = y ⊗ 1` in `A ⊗ ℚ`: some positive multiple of `x - y` vanishes. -/
def RatEq {A : Type*} [AddCommGroup A] (x y : A) : Prop :=
  ∃ ν : ℕ, 0 < ν ∧ ν • x = ν • y

/-! ### Degree maps and the close-pair test -/

/-- **Fixed self-maps `D k` of `S^d`**, meant to be the based cellular maps of degree `k` that
build the telescope (5.3) in the proof of Lemma 5.5. Nothing here says "degree": the invariant
(`OAIInvariant.mapD`, from Proposition 4.8) and the topological inputs each state what they need
about the same maps. -/
structure DegreeMaps (d : ℕ) where
  /-- The map `D k`. -/
  D : ℕ → C(Sphere d, Sphere d)

/-- `D_s = D (s + 1) ∘ ⋯ ∘ D 2`, of intended degree `(s + 1)!`: the composite of the first `s`
maps of the telescope, onto whose last sphere a finite subtelescope retracts (proof of
Lemma 5.5). -/
noncomputable def DegreeMaps.comp {d : ℕ} (δ : DegreeMaps d) : ℕ → C(Sphere d, Sphere d)
  | 0 => ContinuousMap.id _
  | s + 1 => (δ.D (s + 2)).comp (δ.comp s)

/-- **The close-pair test** `C_d = {(x₀, x₁) ∈ S^d × S^d | ⟨x₀, x₁⟩ ≥ 0}` of (6.11), used in the
proof of Proposition 6.6. -/
abbrev ClosePair (d : ℕ) : Type :=
  {z : Sphere d × Sphere d // 0 ≤ inner ℝ (z.1 : EuclideanSpace ℝ (Fin (d + 1))) z.2}

/-! ### Characters -/

/-- The group `Λ` of complex roots of unity of `p`-power order (06:25). -/
def Λ (p : ℕ) : Type := {z : ℂ // ∃ j : ℕ, z ^ (p ^ j) = 1}

/-- `ζ_k = exp(2πi / p^k)`. -/
def ζ (p k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ))

/-- The character `χ_k : ℤ_[p] → μ_{p^k}` with `χ_k(1) = ζ_k`, through `ℤ_[p] → ℤ/p^k`
(06:405-409). -/
def χ (p : ℕ) [Fact p.Prime] (k : ℕ) (g : ℤ_[p]) : ℂ :=
  ζ p k ^ (PadicInt.toZModPow k g).val

/-- `ζ_k` is a `p^k`-th root of unity. -/
theorem ζ_pow_pow (p k : ℕ) : ζ p k ^ (p ^ k) = 1 := by
  rcases eq_or_ne (p ^ k) 0 with h | h
  · rw [h, pow_zero]
  · exact (Complex.isPrimitiveRoot_exp (p ^ k) h).pow_eq_one

/-- Multiplication by `ζ_k` on `Λ`. -/
def Λ.mulζ {p : ℕ} (k : ℕ) (z : Λ p) : Λ p :=
  ⟨ζ p k * z.1, by
    obtain ⟨j, hj⟩ := z.2
    refine ⟨j + k, ?_⟩
    have h1 : ζ p k ^ p ^ (j + k) = 1 := by rw [pow_add, mul_comm, pow_mul, ζ_pow_pow, one_pow]
    have h2 : z.1 ^ p ^ (j + k) = 1 := by rw [pow_add, pow_mul, hj, one_pow]
    rw [mul_pow, h1, h2, one_mul]⟩

/-- `p^k ≠ 0` for a prime `p`, so that `Fin (p ^ k)` has `0`, `1` and wrap-around addition. -/
instance (p k : ℕ) [Fact p.Prime] : NeZero (p ^ k) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- A **cyclic partition** (6.12) `Λ = D₀ ⊔ ⋯ ⊔ D_{m−1}`, `m = p^k`, with `Dᵢ = ζ^i D₀`, given by
the index map `κ : Λ → Fin m`: multiplication by `ζ` raises the index by one, modulo `m`. -/
def IsCyclicPartition (p k : ℕ) [Fact p.Prime] (κ : Λ p → Fin (p ^ k)) : Prop :=
  ∀ z, κ (Λ.mulζ k z) = κ z + 1

/-- For a primitive `n`-th root of unity `ξ`, there is an index map `κ : ℂ → Fin n` such that
multiplication by `ξ` raises the index of every nonzero number by one: choose a representative
`r` of each orbit of `ξ ^ ℕ` and let `κ z` be the exponent `i` with `z = ξ ^ i * r`. -/
theorem exists_index_mul_primitiveRoot {ξ : ℂ} {n : ℕ} [NeZero n] (hξ : IsPrimitiveRoot ξ n) :
    ∃ κ : ℂ → Fin n, ∀ z ≠ 0, κ (ξ * z) = κ z + 1 := by
  have hmod : ∀ i, ξ ^ (i % n) = ξ ^ i := fun i => by rw [hξ.eq_orderOf, pow_mod_orderOf]
  let s : Setoid ℂ :=
    { r := fun a b => ∃ i : ℕ, b = ξ ^ i * a
      iseqv :=
        { refl := fun a => ⟨0, by rw [pow_zero, one_mul]⟩
          symm := by
            rintro a b ⟨i, rfl⟩
            refine ⟨i * (n - 1), ?_⟩
            rw [← mul_assoc, ← pow_add, ← Nat.mul_add_one, Nat.sub_add_cancel NeZero.one_le,
              pow_mul', hξ.pow_eq_one, one_pow, one_mul]
          trans := by
            rintro a b c ⟨i, rfl⟩ ⟨j, rfl⟩
            exact ⟨j + i, by rw [pow_add, mul_assoc]⟩ } }
  let rep : ℂ → ℂ := fun z => (Quotient.mk s z).out
  have hrep : ∀ z, ∃ i : Fin n, z = ξ ^ (i : ℕ) * rep z := by
    intro z
    obtain ⟨i, hi⟩ := Quotient.mk_out' (s₁ := s) z
    exact ⟨⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩, by rw [hmod]; exact hi⟩
  have hrep_mul : ∀ z, rep (ξ * z) = rep z := fun z =>
    congrArg Quotient.out (Quotient.sound (s := s) ⟨1, by rw [pow_one]⟩).symm
  choose κ hκ using hrep
  refine ⟨κ, fun z hz => Fin.ext <| hξ.pow_inj (κ (ξ * z)).isLt (κ z + 1).isLt ?_⟩
  have hr : rep z ≠ 0 := fun h => hz (by rw [hκ z, h, mul_zero])
  refine mul_right_cancel₀ hr ?_
  calc ξ ^ (κ (ξ * z) : ℕ) * rep z = ξ * z := by rw [← hrep_mul z]; exact (hκ _).symm
    _ = ξ ^ ((κ z : ℕ) + 1) * rep z := by rw [pow_succ', mul_assoc, ← hκ z]
    _ = ξ ^ ((κ z + 1 : Fin n) : ℕ) * rep z := by
      rw [Fin.val_add, hmod, pow_add, pow_add, Fin.val_one', hmod]

/-- Cyclic partitions exist (06:396-402): take for `D₀` a transversal of the cosets of `μ_m`. -/
theorem exists_isCyclicPartition (p k : ℕ) [Fact p.Prime] :
    ∃ κ : Λ p → Fin (p ^ k), IsCyclicPartition p k κ := by
  obtain ⟨κ, hκ⟩ := exists_index_mul_primitiveRoot
    (Complex.isPrimitiveRoot_exp (p ^ k) (NeZero.ne (p ^ k)))
  refine ⟨fun z => κ z.1, fun z => hκ z.1 ?_⟩
  obtain ⟨j, hj⟩ := z.2
  rintro h
  rw [h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at hj
  exact zero_ne_one hj

/-! ### Local actions -/

/-- **A continuous action of `ℤ_[p]` on an open subset of a `k`-dimensional real normed space**,
the form in which OpenAI's §§5–6 handle the action after Proposition 5.1: on the
invariant chart subset `O ⊆ ℝ^n`, then on `W = O × ℝ^{d−n} ⊆ ℝ^d`. The ambient space is any
`k`-dimensional space rather than `ℝ^k`, so that `W = O × ℝ^{d−n}` is literally a product. -/
structure LocalAction (p : ℕ) [Fact p.Prime] (k : ℕ) where
  /-- The ambient space. -/
  E : Type
  /-- The ambient space is normed. -/
  [normed : NormedAddCommGroup E]
  /-- The ambient space is a real normed space. -/
  [normedSpace : NormedSpace ℝ E]
  /-- The ambient space is finite-dimensional. -/
  [findim : FiniteDimensional ℝ E]
  /-- It has dimension `k`. -/
  finrank_eq : Module.finrank ℝ E = k
  /-- The open set acted on. -/
  W : Set E
  /-- `W` is open. -/
  isOpen : IsOpen W
  /-- The action. -/
  [act : AddAction ℤ_[p] W]
  /-- The action is jointly continuous. -/
  [cont : ContinuousVAdd ℤ_[p] W]

attribute [instance] LocalAction.normed LocalAction.normedSpace LocalAction.findim LocalAction.act
  LocalAction.cont

namespace LocalAction

variable {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k)

/-- The action is faithful. -/
abbrev Faithful : Prop := FaithfulVAdd ℤ_[p] A.W

/-- The action `g • w = (p^j g) + w` of `ℤ_[p]` on `W`, through `p^j ℤ_[p]`. -/
@[instance_reducible]
def restrictAct (j : ℕ) : AddAction ℤ_[p] A.W where
  vadd g w := ((p : ℤ_[p]) ^ j * g) +ᵥ w
  zero_vadd w := show ((p : ℤ_[p]) ^ j * 0) +ᵥ w = w by rw [mul_zero, zero_vadd]
  add_vadd g h w :=
    show ((p : ℤ_[p]) ^ j * (g + h)) +ᵥ w = ((p : ℤ_[p]) ^ j * g) +ᵥ
      (((p : ℤ_[p]) ^ j * h) +ᵥ w) by rw [mul_add, add_vadd]

/-- **The action of the open subgroup `p^j ℤ_[p]`**, identified with `ℤ_[p]` by `g ↦ p^j g`. -/
def restrict (j : ℕ) : LocalAction p k where
  E := A.E
  finrank_eq := A.finrank_eq
  W := A.W
  isOpen := A.isOpen
  act := A.restrictAct j
  cont := by
    have h : Continuous fun x : ℤ_[p] × A.W => ((p : ℤ_[p]) ^ j * x.1) +ᵥ x.2 :=
      continuous_vadd.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
    exact @ContinuousVAdd.mk _ _ (A.restrictAct j).toVAdd _ _ h

/-- The first coordinate of a point of `W × ℝ^m`, as a point of `W`. -/
def stabFst {m : ℕ} (x : ↥(A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m))))) : A.W :=
  ⟨x.1.1, x.2.1⟩

/-- The first coordinate is continuous. -/
theorem continuous_stabFst (m : ℕ) :
    Continuous (A.stabFst (m := m)) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

/-- The action of `ℤ_[p]` on `W × ℝ^m`, trivial on `ℝ^m`. -/
@[instance_reducible]
def stabilizeAct (m : ℕ) : AddAction ℤ_[p] ↥(A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m)))) where
  vadd g x := ⟨(((g +ᵥ A.stabFst x : A.W) : A.E), x.1.2), (g +ᵥ A.stabFst x).2, mem_univ _⟩
  zero_vadd x := Subtype.ext <| Prod.ext (congrArg Subtype.val (zero_vadd ℤ_[p] (A.stabFst x))) rfl
  add_vadd g h x := Subtype.ext <| Prod.ext (congrArg Subtype.val (add_vadd g h (A.stabFst x))) rfl

/-- **Stabilization** (§5, after Proposition 5.1): the action on `W × ℝ^{d−k}`, trivial on the
second factor, as an action in dimension `d ≥ k`. OpenAI takes `k = n` and an odd `d > n`. -/
def stabilize (d : ℕ) (hd : k ≤ d) : LocalAction p d where
  E := A.E × EuclideanSpace ℝ (Fin (d - k))
  finrank_eq := by
    rw [Module.finrank_prod, A.finrank_eq, finrank_euclideanSpace_fin, Nat.add_sub_cancel' hd]
  W := A.W ×ˢ univ
  isOpen := A.isOpen.prod isOpen_univ
  act := A.stabilizeAct (d - k)
  cont := by
    have h : Continuous fun x : ℤ_[p] × ↥(A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d - k))))) =>
        (⟨(((x.1 +ᵥ A.stabFst x.2 : A.W) : A.E), x.2.1.2), (x.1 +ᵥ A.stabFst x.2).2,
          mem_univ _⟩ : ↥(A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d - k)))))) := by
      refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
      · exact continuous_subtype_val.comp
          (continuous_vadd.comp (continuous_fst.prodMk ((A.continuous_stabFst _).comp
            continuous_snd)))
      · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
    exact @ContinuousVAdd.mk _ _ (A.stabilizeAct (d - k)).toVAdd _ _ h

/-- Passing to an open subgroup keeps the action faithful, since `g ↦ p^j g` is injective. -/
theorem restrict_faithful (j : ℕ) (h : A.Faithful) : (A.restrict j).Faithful := by
  refine ⟨fun {g₁ g₂} hg => ?_⟩
  change ∀ w : A.W, ((p : ℤ_[p]) ^ j * g₁) +ᵥ w = ((p : ℤ_[p]) ^ j * g₂) +ᵥ w at hg
  have hp : ((p : ℤ_[p]) ^ j) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  exact mul_left_cancel₀ hp (h.eq_of_vadd_eq_vadd hg)

/-- Stabilization keeps the action faithful. -/
theorem stabilize_faithful (d : ℕ) (hd : k ≤ d) (h : A.Faithful) : (A.stabilize d hd).Faithful := by
  refine ⟨fun {g₁ g₂} hg => h.eq_of_vadd_eq_vadd fun w => Subtype.ext ?_⟩
  let x : ↥(A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d - k))))) :=
    ⟨(w.1, 0), w.2, mem_univ _⟩
  exact congrArg (fun y : ↥(A.W ×ˢ (univ : Set (EuclideanSpace ℝ (Fin (d - k))))) => y.1.1) (hg x)

/-- Stabilization keeps `W` connected. -/
theorem stabilize_isConnected (d : ℕ) (hd : k ≤ d) (h : IsConnected A.W) :
    IsConnected (A.stabilize d hd).W :=
  h.prod isConnected_univ

/-! #### The one-point compactification, the orbit space and the collapse (Lemma 5.2) -/

/-- The action extended to `W⁺ = W ∪ {∞}`, fixing `∞` (Lemma 5.2). -/
instance plusAction : AddAction ℤ_[p] (OnePoint A.W) where
  vadd g x := x.elim ∞ fun w => ((g +ᵥ w : A.W) : OnePoint A.W)
  zero_vadd x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe w => exact congrArg ((↑) : A.W → OnePoint A.W) (zero_vadd ℤ_[p] w)
  add_vadd g h x := by
    induction x using OnePoint.rec with
    | infty => rfl
    | coe w => exact congrArg ((↑) : A.W → OnePoint A.W) (add_vadd g h w)

@[simp] theorem vadd_infty (g : ℤ_[p]) : g +ᵥ (∞ : OnePoint A.W) = ∞ := rfl

@[simp] theorem vadd_coe (g : ℤ_[p]) (w : A.W) :
    g +ᵥ (w : OnePoint A.W) = ((g +ᵥ w : A.W) : OnePoint A.W) := rfl

/-- The orbit space `Y = W⁺ / ℤ_[p]`. -/
abbrev Y : Type := AddAction.orbitRel.Quotient ℤ_[p] (OnePoint A.W)

/-- The orbit map `q : W⁺ → Y`. -/
def q : C(OnePoint A.W, A.Y) := ⟨Quotient.mk _, continuous_quotient_mk'⟩

/-- `y∞ = q(∞)`. -/
def yinf : A.Y := A.q ∞

/-- The sphere `S^k` as the one-point compactification of the ambient space. -/
def sphereEquiv : OnePoint A.E ≃ₜ Sphere k :=
  (onePointEquivSphereOfFinrankEq (V := A.E) (ι := Fin (k + 1))
    (by simp [A.finrank_eq])).trans
    (Homeomorph.subtype (Homeomorph.refl _) fun x => by simp)

/-- **The collapse** `c : S^k → W⁺` of Lemma 5.2: the identity on `W` and `∞` elsewhere, with
`S^k` the one-point compactification of the ambient space. -/
def c : C(Sphere k, OnePoint A.W) :=
  ⟨collapse A.W ∘ A.sphereEquiv.symm,
    (continuous_collapse A.W A.isOpen).comp A.sphereEquiv.symm.continuous⟩

/-- The composite `qc : S^k → Y`. -/
def qc : C(Sphere k, A.Y) := A.q.comp A.c

end LocalAction

/-! ### Sheet multipliers -/

/-- **The output of Lemma 5.6 at level `j`**: a nonempty open `V ⊆ Y ∖ {y∞}` and a locally
constant function `β` on `q⁻¹(V)` with values of modulus one and `β(g + w) = χ_j(g) β(w)` (5.4).
OpenAI's `β` takes values in `{1, ζ, …, ζ^{m−1}}`; only `|β| = 1`, local constancy and (5.4) are
used (in the proof of Proposition 6.7). -/
structure SheetMultiplier {p : ℕ} [Fact p.Prime] {k : ℕ} (A : LocalAction p k) (j : ℕ)
    (V : Set A.Y) : Prop where
  /-- `V` is open. -/
  isOpen : IsOpen V
  /-- `V` is nonempty. -/
  nonempty : V.Nonempty
  /-- `V` avoids `y∞`. -/
  yinf_notMem : A.yinf ∉ V
  /-- The multiplier `β` on `q⁻¹(V)`, locally constant, of modulus one, satisfying (5.4). -/
  exists_beta : ∃ β : OnePoint A.W → ℂ,
    IsLocallyConstant ((A.q ⁻¹' V).domRestrict β) ∧ (∀ w ∈ A.q ⁻¹' V, ‖β w‖ = 1) ∧
      ∀ (g : ℤ_[p]) (w : OnePoint A.W), w ∈ A.q ⁻¹' V → β (g +ᵥ w) = χ p j g * β w

end

end HilbertSmith.Interface

import HilbertSmith.Interface.Forms
import HilbertSmith.Interface.Spaces

/-!
# OpenAI's invariant as an interface

The proof of p-adic exclusion in §§5–6 of OpenAI's preprint uses the Witt groups of sheaves of
§§2–4 only through a short list of properties. This file states them as structures, in the way
HS_proof's `HSFormal.LTheory.LowerLTheory` states the L-theory that HS_proof's proof uses
(plan item B1, with PLAN §3.2's changes).

* `OAIInvariant d δD`: the action-independent part, for one odd `d ≥ 3`: the Witt group
  `E_d(X) = W_d(𝒯(X))` of test spaces with pushforward and homotopy invariance, the lattice of
  Theorem 4.7, the action of degree (Proposition 4.8), the quotient categories
  `𝒬_U(X) = 𝒯(X)/𝒯(U)` with their duality and Witt classes, and the integral localization
  isomorphism `ℓ_U` of Proposition 4.9 with its naturality.
* `Admissible`: a compact test `t : Y → X` with a good neighbourhood `U` of `b_t` (06:101-107,
  06:212).
* `OrbitCharacterTheory I OP`: the facts of §6 about the test form `(A_t, α_t)` of (6.4) and its
  character projectors: its class, the projector identities (6.6), covariance (Proposition 6.5)
  and the sheet twist (Proposition 6.7). `OP` is the orientation-preservation predicate on local
  actions, a parameter (PLAN §3.2, change 4).
* `OAIInterface`: the two structures for every odd `d = 2j + 3`, with the degree maps and `OP`.

Field tags, from B1: **[SHEAF]** holds in OpenAI's model through the sheaf theory of §§2–4;
**[FORMAL]** holds for the Witt group of any category with duality; **[TOP]** is topology without
sheaves. Every field's docstring says why OpenAI's model satisfies it, with the preprint's
numbering (and `06:` for lines of `sections/06-character-classes.tex`).

Non-vacuity: every field holds for OpenAI's `E_d = W_d(𝒯(-))` and `𝒬_U(X) = 𝒯(X)/𝒯(U)` by the
cited result. `E`, `Q` and `WQ` are total, so that no field needs a dependent type. Off test spaces,
and for non-open `U`, a model may take zero categories and zero groups: every field either assumes
`IsTest` (or `Admissible`), or, like `wmap_cls`, holds for any duality-preserving functor, the zero
functor included (plan item B-P, "Lean-level obligations"), or, like `lattice`, `u_nontorsion` and
`mapD`, concerns only `S^d`, a test space by `isTest_sphere`. There is also a size obligation:
`E X`, `Q X U` (with `Category.{0}`) and `WQ X U` live in `Type`, so a model replaces the test
categories by small skeleta (they are essentially small, 02:91-96, 03:253-257) and must prove the
Hom types of the quotient categories small. The zero model (every group and category zero)
satisfies every field except `u_nontorsion`; with `form_cls`, trivial quotient categories are
excluded too. So the hypotheses carry content. A wrongly stated field would make the interface
unsatisfiable, never unsound: the conclusion of the formal layer is a fixed Mathlib statement.
-/

namespace HilbertSmith.Interface

open CategoryTheory CategoryTheory.Limits Opposite Topology Set

noncomputable section

/-- **OpenAI's invariant, as §§5–6 use it**, for one odd `d ≥ 3` and the fixed degree maps `δD`.
-/
structure OAIInvariant (d : ℕ) (δD : DegreeMaps d) where
  /-- [TOP] The test spaces of §2.1: locally compact, finite-dimensional, separable metrizable
  spaces that are finite polyhedra, spaces homeomorphic to one, open subsets of such, or finite
  products of these. Abstract here; a model fixes it. -/
  IsTest : (X : Type) → [TopologicalSpace X] → Prop
  /-- [TOP] `S^d` is (homeomorphic to) a compact polyhedron, the boundary of a simplex. -/
  isTest_sphere : IsTest (Sphere d)
  /-- [TOP] `C_d` is compact semialgebraic, hence homeomorphic to a finite polyhedron (06:359).
  The weakest point of non-vacuity (B1 §2.7): a model needs semialgebraic triangulation here, or
  another proof of Proposition 6.6. -/
  isTest_closePair : IsTest (ClosePair d)
  /-- [SHEAF] `E_d(X) = W_d(𝒯(X))`, the Witt group of the test category of Definition 2.1 in
  degree `d` ((2.9), `cat:witt-indexing`). Only degree `d` enters §§5–6. -/
  E : (X : Type) → [TopologicalSpace X] → Type
  /-- [SHEAF] `E_d(X)` is an abelian group (a Witt group). -/
  [grp : ∀ (X : Type) [TopologicalSpace X], AddCommGroup (E X)]
  /-- [SHEAF] Pushforward `g_*`: by Proposition 2.5, direct image `Rg_! ≃ Rg_*` is an exact
  functor `𝒯(X) → 𝒯(Y)` commuting with Verdier duality, so it acts on Witt groups. -/
  map : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y], C(X, Y) → E X →+ E Y
  /-- [SHEAF] Proposition 2.5: the identity acts as the identity. -/
  map_id : ∀ (X : Type) [TopologicalSpace X], IsTest X →
    map (ContinuousMap.id X) = AddMonoidHom.id _
  /-- [SHEAF] Proposition 2.5 (02:300-312): direct images are compatible with composition. -/
  map_comp : ∀ {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z],
    IsTest X → IsTest Y → IsTest Z → ∀ (f : C(X, Y)) (g : C(Y, Z)),
    map (g.comp f) = (map g).comp (map f)
  /-- [SHEAF] Theorem 2.9 (homotopy invariance; statement 02:701-714, proof 02:716-736): homotopic
  maps of test spaces induce equal maps `E_r(X) → E_r(Y)`. -/
  map_homotopic : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y],
    IsTest X → IsTest Y → ∀ {f g : C(X, Y)}, f.Homotopic g → map f = map g
  /-- [SHEAF] The orientation class `u_d ∈ E_d(S^d)`: the class of the constant sheaf with the
  orientation pairing (§4, used in Theorem 4.7; 05:84-85: "Its orientation form represents
  `u_d`"). -/
  u : E (Sphere d)
  /-- [SHEAF] The denominator `L_d = 2^{e_d}` of Theorem 4.7 (04:370-386); only `0 < L` is
  used. -/
  L : ℕ
  /-- [SHEAF] Theorem 4.7: `L_d` is a positive power of `2` (04:373-374). -/
  L_pos : 0 < L
  /-- [SHEAF] Theorem 4.7, both lines of its display at once: `E_d(S^d) ⊗ ℚ = ℚ ū_d`, and the
  image of `E_d(S^d)` in `E_d(S^d) ⊗ ℚ` lies in `L_d⁻¹ ℤ ū_d`; that is, `L_d x ⊗ 1` is an integer
  multiple of `ū_d` for every `x`. -/
  lattice : ∀ x : E (Sphere d), ∃ a : ℤ, RatEq (L • x) (a • u)
  /-- [SHEAF] `ū_d ≠ 0`: by Proposition 4.5, `E_d(S^d) ⊗ ℚ` is one-dimensional, and by
  Theorem 4.7 it is spanned by `ū_d` (used at 06:496-498). -/
  u_nontorsion : ∀ ν : ℕ, 0 < ν → ν • u ≠ 0
  /-- [SHEAF] Proposition 4.8 (action of degree) for the fixed maps: `D k` has degree `k`, so
  `(D k)_* ū_d = k ū_d` in `E_d(S^d) ⊗ ℚ`. -/
  mapD : ∀ k : ℕ, 2 ≤ k → RatEq (map (δD.D k) u) ((k : ℤ) • u)
  /-- [SHEAF] The Verdier quotient `𝒬_U(X) = 𝒯(X)/𝒯(U)` (06:212-215), an additive category
  (it is triangulated). -/
  Q : (X : Type) → [TopologicalSpace X] → Set X → Type
  /-- [SHEAF] `𝒬_U(X)` is a category. -/
  [cat : ∀ (X : Type) [TopologicalSpace X] (U : Set X), Category.{0} (Q X U)]
  /-- [SHEAF] `𝒬_U(X)` is preadditive (a Verdier quotient of a triangulated category is
  triangulated, hence additive). -/
  [preadd : ∀ (X : Type) [TopologicalSpace X] (U : Set X), Preadditive (Q X U)]
  /-- [SHEAF] `𝒬_U(X)` has binary biproducts, for orthogonal sums of forms (06:264-288). -/
  [biprod : ∀ (X : Type) [TopologicalSpace X] (U : Set X), HasBinaryBiproducts (Q X U)]
  /-- [SHEAF] The duality `D_{X,d}` that `𝒬_U(X)` inherits from Verdier duality (Proposition 2.3,
  Theorem 3.3: the germ isomorphisms respect open restriction of duality; Theorem 3.4). -/
  dual : ∀ (X : Type) [TopologicalSpace X] (U : Set X), Duality (Q X U)
  /-- [SHEAF] The duality is additive (it is exact, Proposition 2.3). -/
  [dualAdd : ∀ (X : Type) [TopologicalSpace X] (U : Set X), (dual X U).D.Additive]
  /-- [FORMAL] The Witt group `W_d(𝒬_U(X))`. -/
  WQ : (X : Type) → [TopologicalSpace X] → Set X → Type
  /-- [FORMAL] `W_d(𝒬_U(X))` is an abelian group. -/
  [wgrp : ∀ (X : Type) [TopologicalSpace X] (U : Set X), AddCommGroup (WQ X U)]
  /-- [FORMAL] Classes of forms in `W_d(𝒬_U(X))`, with the relations of `WittClasses`. -/
  witt : ∀ (X : Type) [TopologicalSpace X] (U : Set X), WittClasses (dual X U) (WQ X U)
  /-- [SHEAF] Proposition 4.9: for odd `d ≥ 3` and a nonempty contractible open `U` of a test space
  `X`, the quotient functor induces an integral isomorphism `ℓ_U : E_d(X) ≅ W_d(𝒬_U(X))`
  (Witt localization, Theorem 3.4, with `E_d(U) = E_d(pt) = 0` and the split injectivity of
  `E_{d−1}(U) → E_{d−1}(X)`). -/
  ℓ : ∀ (X : Type) [TopologicalSpace X] (U : Set X), IsTest X → IsGood U → E X ≃+ WQ X U
  /-- [SHEAF] For `g : X → X'` with `g(U) ⊆ U'`, direct image induces a duality-preserving functor
  `ḡ_* : 𝒬_U(X) → 𝒬_{U'}(X')` (06:305-315, from Proposition 2.5 and Theorem 3.4). For `g = id`
  and `U ⊆ U'` it is the quotient functor that OpenAI uses to show that Definition 6.3 does not
  depend on `U` (06:245-250). -/
  pushQ : ∀ {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (g : C(X, X'))
    (U : Set X) (U' : Set X'), MapsTo g U U' → DualFunctor (dual X U) (dual X' U')
  /-- [FORMAL] The map of Witt groups induced by `ḡ_*`. -/
  wmap : ∀ {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (g : C(X, X'))
    (U : Set X) (U' : Set X'), MapsTo g U U' → WQ X U →+ WQ X' U'
  /-- [FORMAL] A duality-preserving functor sends the class of a form to the class of the pushed
  form. -/
  wmap_cls : ∀ {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (g : C(X, X'))
    (U : Set X) (U' : Set X') (h : MapsTo g U U') (φ : Form (dual X U)),
    wmap g U U' h ((witt X U).cls φ) = (witt X' U').cls ((pushQ g U U' h).mapForm φ)
  /-- [SHEAF] Naturality of `ℓ` (Proposition 4.9, last sentence): the square with `g_*` and
  `ḡ_*` commutes (the "commuting square on Witt groups" of 06:311-315). -/
  ℓ_natural : ∀ {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (g : C(X, X'))
    (U : Set X) (U' : Set X') (hX : IsTest X) (hX' : IsTest X') (hU : IsGood U)
    (hU' : IsGood U') (h : MapsTo g U U') (x : E X),
    ℓ X' U' hX' hU' (map g x) = wmap g U U' h (ℓ X U hX hU x)

attribute [instance] OAIInvariant.grp OAIInvariant.cat OAIInvariant.preadd OAIInvariant.biprod
  OAIInvariant.dualAdd OAIInvariant.wgrp

/-- `(t, U)` is an **admissible compact test** (06:101-107, 06:210-215): `X` is a compact Hausdorff
test space, `b_t = t(y∞)` has a basis of good neighbourhoods, and `U` is a good neighbourhood of
`b_t`. -/
structure Admissible {d : ℕ} {δD : DegreeMaps d} (I : OAIInvariant d δD) {p : ℕ} [Fact p.Prime]
    (A : LocalAction p d) {X : Type} [TopologicalSpace X] (t : C(A.Y, X)) (U : Set X) :
    Prop where
  /-- `X` is a test space. -/
  isTest : I.IsTest X
  /-- `X` is compact. -/
  compact : CompactSpace X
  /-- `X` is Hausdorff. -/
  t2 : T2Space X
  /-- `b_t` has a basis of good neighbourhoods. -/
  basis : HasGoodBasisAt (t A.yinf)
  /-- `U` is good. -/
  good : IsGood U
  /-- `U` contains `b_t`. -/
  mem : t A.yinf ∈ U

/-- **The sheaf facts of §6**, for every local action `A` on an open subset of a `d`-dimensional
space and every admissible test `t : Y → X`. `OP` is the orientation-preservation predicate on
local actions.

Non-vacuity: with OpenAI's `A_t = Rf_{t*}ℂ_{S^d}`, `f_t = t ∘ q ∘ c` (6.4), every field holds by the
cited result. The structure quantifies over every `LocalAction`, while §6 has standing hypotheses
(06:3-14: `O` connected, the action faithful and orientation-preserving, `deg(aqc) = 1`). That is
fine, because each field needs only part of them, and assumes that part: Lemma 6.1 (`proj`,
`proj_mul`, `proj_sum`) needs only `W⁺` compact metrizable (06:55-58), which holds for every local
action; Lemma 6.2 (`proj_adj`) needs only orientation preservation (06:160-170), assumed as `OP A`;
Proposition 6.7 (`twist`) needs only the multiplier `β` (06:421-435), assumed as
`SheetMultiplier`. -/
structure OrbitCharacterTheory {d : ℕ} {δD : DegreeMaps d} (I : OAIInvariant d δD)
    (OP : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ}, LocalAction p k → Prop) where
  /-- [SHEAF] The test form (6.4): the image in `𝒬_U(X)` of `A_t = Rf_{t*}ℂ_{S^d}`,
  `f_t = t ∘ q ∘ c`, with `α_t` the pushforward of the orientation pairing of `S^d` with
  coefficient form `B(z, w) = Re(z w̄)`. `A_t` lies in `𝒯(X)` (two copies of a compact polyhedron
  generator), and its form exists by Propositions 2.3 and 2.5 (06:118-120). The orientation of
  `S^d` is the one that defines `u` (05:82-85, 06:13-14); with the opposite orientation `form_cls`
  fails by a sign, which a model fixes by replacing `u` with `−u`. -/
  form : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) {X : Type} [TopologicalSpace X],
    C(A.Y, X) → ∀ U : Set X, Form (I.dual X U)
  /-- [SHEAF] `[A_t, α_t] = 2 (f_t)_* u_d`, read through `ℓ_U`, which is induced by the quotient
  functor `𝒯(X) → 𝒬_U(X)` (Proposition 4.9). OpenAI states it for `t = a` (06:486-489): "the
  coefficient form `B` is the orthogonal sum of two positive real lines"; the argument is the same
  for every `t`, by Proposition 2.5. The factor `2` is OpenAI's; the formal layer only needs it to
  be positive (it enters the bound `m > 4 L_d`). -/
  form_cls : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) {X : Type} [TopologicalSpace X]
    (t : C(A.Y, X)) (U : Set X) (h : Admissible I A t U),
    I.ℓ X U h.isTest h.good (2 • I.map (t.comp A.qc) I.u) = (I.witt X U).cls (form A t U)
  /-- [SHEAF] The character projectors `eᵢ` for a partition `κ : Λ → Fin m` of the characters
  (06:210-217): germs at `X ∖ U` of the projectors of `B_{Dᵢ} ⊆ A_t|_{X ∖ b_t}`, from Lemma 6.1,
  the identification (6.5) and Theorem 3.3. Lemma 6.1 uses Lemma 5.4 again, in its sheaf form
  `Rr_* ℝ = r_* ℝ` for the orbit map of `W⁺` (06:55-58); the topological input `OrbitNull` (or a
  separate topological `OrbitInjectivity`) does not cover that use, which stays inside this
  field. -/
  proj : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) {X : Type} [TopologicalSpace X]
    (t : C(A.Y, X)) (U : Set X) {m : ℕ}, (Λ p → Fin m) → Fin m →
    ((form A t U).obj ⟶ (form A t U).obj)
  /-- [SHEAF] (6.6), first identity `eᵢ eⱼ = δᵢⱼ eᵢ`: the character decomposition (6.1) and its
  compatibility with `Rt_*` (6.2) of Lemma 6.1, carried to the quotient by Theorem 3.3. Lemma 6.1
  rests on the sheaf form of Lemma 5.4, `Rr_* = r_*` (06:55-58), see `proj`. -/
  proj_mul : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) {X : Type} [TopologicalSpace X]
    (t : C(A.Y, X)) (U : Set X), Admissible I A t U → ∀ {m : ℕ} (κ : Λ p → Fin m) (i j : Fin m),
    proj A t U κ i ≫ proj A t U κ j = if i = j then proj A t U κ i else 0
  /-- [SHEAF] (6.6), second identity `∑ᵢ eᵢ = 1` (Lemma 6.1, Theorem 3.3). -/
  proj_sum : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) {X : Type} [TopologicalSpace X]
    (t : C(A.Y, X)) (U : Set X), Admissible I A t U → ∀ {m : ℕ} (κ : Λ p → Fin m),
    ∑ i, proj A t U κ i = 𝟙 _
  /-- [SHEAF] (6.6), third identity `eᵢ† = eᵢ`: Lemma 6.2 (real orthogonality). It needs the
  action to preserve orientation: then `T† = T⁻¹` (06:160-170). -/
  proj_adj : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d), OP A → ∀ {X : Type}
    [TopologicalSpace X] (t : C(A.Y, X)) (U : Set X), Admissible I A t U →
    ∀ {m : ℕ} (κ : Λ p → Fin m) (i : Fin m), (form A t U).adj (proj A t U κ i) = proj A t U κ i
  /-- [SHEAF] The identification in the proof of Proposition 6.5 (06:316-342): for `g : X → X'`
  with `g(U) ⊆ U'`, `ḡ_*` carries `(A_t, α_t)` isometrically to `(A_{gt}, α_{gt})` ("composition of
  proper direct images identifies the pushed total form with `(A_{gt}, α_{gt})`") and the
  projectors `eᵢ(t)` to `eᵢ(gt)` (the germ theorem, Theorem 3.3). An isometry `e` conjugates
  `F(eᵢ(t))` to `eᵢ(gt)`; the formula `e⁻¹ F(eᵢ(t)) e = eᵢ(gt)` is one of three equivalent ways
  to write that, so the "direction" doubt raised in B1 does not affect the formal layer. -/
  push : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) {X X' : Type} [TopologicalSpace X]
    [TopologicalSpace X'] (t : C(A.Y, X)) (g : C(X, X')) (U : Set X) (U' : Set X'),
    Admissible I A t U → Admissible I A (g.comp t) U' → ∀ hg : MapsTo g U U',
    ∃ e : ((I.pushQ g U U' hg).mapForm (form A t U)).Isometry (form A (g.comp t) U'),
      ∀ {m : ℕ} (κ : Λ p → Fin m) (i : Fin m),
        e.iso.inv ≫ (I.pushQ g U U' hg).F.map (proj A t U κ i) ≫ e.iso.hom =
          proj A (g.comp t) U' κ i
  /-- [SHEAF, given the sheet multiplier `β` of Lemma 5.6 (`SheetMultiplier`)] The proof of
  Proposition 6.7 (06:421-442): if `h` is constant off a sheet region `V`, multiplication by `β`
  is an isometry of `(A_h, α_h)` over `X ∖ {b}` (it is a real isometry since `|β| = 1`) with
  `T M_β = M_{ζ⁻¹} M_β T`, so it conjugates `eᵢ` to `e_{i−1}`; by Theorem 3.3 it is an isometry
  in `𝒬_U(X)`. The index shift is OpenAI's (`i − 1`, indices mod `m`); the formal layer only uses
  that some isometry shifts the index by one, so `i + 1` would serve equally. -/
  twist : ∀ {p : ℕ} [Fact p.Prime] (A : LocalAction p d) (k : ℕ) (V : Set A.Y),
    SheetMultiplier A k V → ∀ {X : Type} [TopologicalSpace X] (h : C(A.Y, X)),
    (∀ y ∉ V, h y = h A.yinf) → ∀ (U : Set X), Admissible I A h U →
    ∀ κ : Λ p → Fin (p ^ k), IsCyclicPartition p k κ →
    ∃ σ : (form A h U).Isometry (form A h U),
      ∀ i, σ.iso.inv ≫ proj A h U κ i ≫ σ.iso.hom = proj A h U κ (i - 1)

/-- **The interface** for every odd `d = 2j + 3`: the degree maps, the orientation predicate, and
for each `j` the invariant and the character theory. -/
structure OAIInterface where
  /-- The degree maps `D k` on `S^{2j+3}`. -/
  δD : ∀ j : ℕ, DegreeMaps (2 * j + 3)
  /-- Orientation preservation of a local action: every element of `ℤ_[p]` acts by an
  orientation-preserving homeomorphism of `W` (PLAN §3.2: a parameter of the route). Whether a
  homeomorphism of `W` preserves orientation does not depend on which of the two orientations of
  the ambient space `A.E` (or of `S^d`, through `LocalAction.sphereEquiv`) is used to test it, so
  `OP` involves no choice of orientation. (For a disconnected `W` other orientations of `W` exist,
  such as one that differs on two components swapped by an element; `OP` uses only those that
  come from `A.E`.) -/
  OP : ∀ {p : ℕ} [Fact p.Prime] {k : ℕ}, LocalAction p k → Prop
  /-- The invariant `E_{2j+3}`. -/
  inv : ∀ j : ℕ, OAIInvariant (2 * j + 3) (δD j)
  /-- The character theory in degree `2j + 3`. -/
  chars : ∀ j : ℕ, OrbitCharacterTheory (inv j) OP

end

end HilbertSmith.Interface

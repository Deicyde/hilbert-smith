# OpenAI preprint source map

The adopted source is OpenAI, *The Hilbert--Smith conjecture in every
finite dimension*, September 23, 2026 (oai-math #304).

- Adopted revision: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
  (openai/math `main` at 2026-10-12).
- [Paper PDF at adopted
  revision](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/paper.pdf)
  (604307 bytes).
- [LaTeX source at adopted
  revision](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build).

Line spans below are 1-based within the named file under `build/`.
Labels are the paper's own `\label` keys. Remarks without formal
content are folded into chapter prose rather than given articles.

## Section 1: Introduction (`sections/01-introduction.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `cor:lie` | 9-14 | Hilbert--Smith conjecture | [Hilbert--Smith conjecture](../roadmap/main-theorem/hilbert-smith-conjecture.md) |
| `thm:main` | 30-35 | $p$-adic exclusion | [$p$-adic exclusion](../roadmap/main-theorem/padic-exclusion.md) |
| (unlabelled) | 42-55 | Almost-periodic flow consequence | [Almost-periodic flow](../roadmap/main-theorem/almost-periodic-flow.md) |
| `intro:lattice` | 170-175 | Lattice inclusion preview | Prose in [sphere lattice](../roadmap/sphere-lattice/sphere-lattice.md) |

## Section 2: Sheaf categories (`sections/02-categories.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `def:test-categories` | 29-57 | Test categories $\T^0,\T,\Pcat^0,\Pcat$ | [Test categories](../roadmap/sheaf-categories/test-categories.md) |
| `cat:simplex-generators` | 98-143 | Simplex generators, summand closure | [Simplex generators](../roadmap/sheaf-categories/simplex-generators.md) |
| `prop:test-duality` | 182-286 | Duality, biduality, compact support | [Verdier duality on test categories](../roadmap/sheaf-categories/test-duality.md) |
| `cat:restriction-caution` | 288-298 | Restriction caution (remark) | Prose in [chapter](../roadmap/sheaf-categories/README.md) |
| `prop:test-pushforward` | 300-376 | Direct images, open extension | [Direct images and open extension](../roadmap/sheaf-categories/test-pushforward.md) |
| `cat:symmetric-cone` | 435-479 | Symmetric cone | [Symmetric cone](../roadmap/sheaf-categories/symmetric-cone.md) |
| `cat:interval-products` | 505-608 | Products with the interval | [Products with the interval](../roadmap/sheaf-categories/interval-products.md) |
| `cat:endpoint-forms` | 623-699 | Two endpoint forms | [Two endpoint forms](../roadmap/sheaf-categories/endpoint-forms.md) |
| `thm:homotopy` | 701-739 | Homotopy invariance | [Homotopy invariance](../roadmap/sheaf-categories/homotopy-invariance.md) |

## Section 3: Localization (`sections/03-localization.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `lem:cutoff` | 30-110 | Cutoff | [Cutoff](../roadmap/localization/cutoff.md) |
| `prop:compact-support` | 114-143 | Objects supported in an open set | [Objects supported in an open set](../roadmap/localization/compact-support.md) |
| `thm:germs` | 165-219 | Germ description | [Germ description](../roadmap/localization/germs.md) |
| `thm:witt-localization` | 227-293 | Witt localization | [Witt localization](../roadmap/localization/witt-localization.md) |
| `prop:open-cover` | 301-334 | Open cover dense inclusion | [Open cover dense inclusion](../roadmap/localization/open-cover.md) |
| `loc:eq-adjacent-shifts` | 366-378 | Adjacent shifts in dense subcategories | [Adjacent shifts](../roadmap/localization/adjacent-shifts.md) |
| `thm:dense-doubling` | 344-460 | Dense doubling | [Dense doubling](../roadmap/localization/dense-doubling.md) |
| `loc:cor-open-cover-bound` | 462-472 | Open-cover exponent-two bound | [Open-cover bound](../roadmap/localization/open-cover-bound.md) |

## Section 4: Sphere lattice (`sections/04-lattice.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `lat:point-groups` | 20-63 | Point calculation | [Point groups](../roadmap/sphere-lattice/point-groups.md) |
| `lat:finite-chases` | 72-122 | Finite diagram chases | [Finite diagram chases](../roadmap/sphere-lattice/finite-chases.md) |
| `thm:bounded-comparison` | 125-185 | Bounded comparison | [Bounded comparison](../roadmap/sphere-lattice/bounded-comparison.md) |
| `lat:exponent-bookkeeping` | 187-199 | Exponent bookkeeping (remark) | Prose in [bounded comparison](../roadmap/sphere-lattice/bounded-comparison.md) |
| `prop:sphere-rank` | 203-251 | Rational sphere calculation | [Rational sphere calculation](../roadmap/sphere-lattice/sphere-rank.md) |
| `prop:generic-signature` | 262-368 | Signature on a finite relation | [Signature on a finite relation](../roadmap/sphere-lattice/generic-signature.md) |
| `thm:sphere-lattice` | 370-398 | Fixed sphere lattice | [Fixed sphere lattice](../roadmap/sphere-lattice/sphere-lattice.md) |
| `prop:degree-action` | 406-485 | Action of degree | [Action of degree](../roadmap/sphere-lattice/degree-action.md) |
| `prop:contractible-quotient` | 487-529 | Contractible set localized away | [Contractible quotient](../roadmap/sphere-lattice/contractible-quotient.md) |

## Section 5: Local tests (`sections/05-local-tests.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `prop:chart-reduction` | 14-73 | Invariant chart subset | [Invariant chart subset](../roadmap/local-tests/chart-reduction.md) |
| `lem:collapse` | 88-133 | Collapse and compactification | [Collapse and compactification](../roadmap/local-tests/collapse.md) |
| `lem:averaged-test` | 135-183 | Averaged degree-one test | [Averaged degree-one test](../roadmap/local-tests/averaged-test.md) |
| `lem:orbit-injectivity` | 209-275 | Rational orbit pullback | [Rational orbit pullback](../roadmap/local-tests/orbit-injectivity.md) |
| `lem:odd-sphere-null` | 287-377 | Killing a rationally trivial map | [Odd-sphere nullhomotopy](../roadmap/local-tests/odd-sphere-null.md) |
| `lem:finite-sheets` | 386-434 | Finite quotient sheets | [Finite quotient sheets](../roadmap/local-tests/finite-sheets.md) |
| `top:neighborhood-extension` | 440-471 | Extending a homotopy | [Homotopy extension](../roadmap/local-tests/neighborhood-extension.md) |
| `prop:move-test` | 478-517 | Moving a test into an open set | [Moving a test](../roadmap/local-tests/move-test.md) |
| `top:proper-test-interface` | 519-538 | Source of a restricted test (remark) | Prose in [chapter](../roadmap/local-tests/README.md) |

## Section 6: Character classes (`sections/06-character-classes.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `lem:character-coproduct` | 37-99 | Character coproducts | [Character coproducts](../roadmap/character-classes/character-coproduct.md) |
| `lem:orthogonality` | 150-203 | Real orthogonality | [Real orthogonality](../roadmap/character-classes/orthogonality.md) |
| `def:character-classes` | 225-250 | Character classes | [Character classes](../roadmap/character-classes/character-classes.md) |
| `prop:sum-classes` | 252-291 | Sum of the character classes | [Sum of the character classes](../roadmap/character-classes/sum-classes.md) |
| `prop:class-covariance` | 295-343 | Covariance on compact tests | [Covariance of character classes](../roadmap/character-classes/class-covariance.md) |
| `prop:class-homotopy` | 345-392 | Homotopy of character classes | [Homotopy of character classes](../roadmap/character-classes/class-homotopy.md) |
| `prop:equal-parts` | 411-443 | Equality for a concentrated test | [Equal parts](../roadmap/character-classes/equal-parts.md) |
| `thm:contradiction` | 445-500 | Contradiction on the invariant chart | [Contradiction on the invariant chart](../roadmap/character-classes/contradiction.md) |
| (unlabelled) | 502-516 | Proof of `thm:main` | Proof sketch in [$p$-adic exclusion](../roadmap/main-theorem/padic-exclusion.md) |
| (unlabelled) | 518-527 | Proof of `cor:lie` | Proof sketch in [Hilbert--Smith conjecture](../roadmap/main-theorem/hilbert-smith-conjecture.md) |

## Appendix A: Duality signs (`appendices/duality-signs.tex`)

| Label | Lines | Content | Article |
| --- | --- | --- | --- |
| `cat:product-shift-sign` | 122-171 | Suspending the first product input | [Product shift sign](../roadmap/sheaf-categories/product-shift-sign.md) |
| (unlabelled) | 16-121, 173-226 | Sign conventions, endpoint normalization | [Sign conventions](../roadmap/sheaf-categories/sign-conventions.md) |

## Assumptions

Reading assumptions fixed by this map, to revisit if the source moves:

- Joint continuity of an action is used interchangeably with a
  continuous homomorphism into $\Homeo(M)$ with the compact-open
  topology (Section 1, lines 37-40).
- Rational cohomology of compact metrizable spaces means Cech
  cohomology identified with constant-sheaf cohomology (Section 5,
  lines 189-207).
- Figure `fig:local-test` (`figures/local-test.tex`) is a schematic
  of the composite $S^d \to W^+ \to Y \to X$ with no formal content;
  no article covers it.
- Remarks `cat:restriction-caution`, `lat:exponent-bookkeeping`, and
  `top:proper-test-interface` carry no independent formal content and
  live in chapter or article prose as noted above.

## Uncovered prerequisites

None. Every load-bearing external prerequisite has a background
article; see the [background map](background.md). Survey-only
references are excluded in the [coverage contract](../coverage/README.md).

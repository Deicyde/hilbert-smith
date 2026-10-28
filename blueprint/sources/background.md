# Background reference map

External results the preprint uses. Locators are the preprint's own
`references.bib` keys plus pinpoints; the bibliography itself lives
with the source. Each load-bearing item has one background article;
survey-only items are excluded in the
[coverage contract](../coverage/README.md).

## Load-bearing references

| Reference | Pinpoint | Article | Used by |
| --- | --- | --- | --- |
| `Newman1931`, `Pardon2019` pp. 2-3 | Periodic rigidity | [Newman rigidity](../roadmap/background/newman-rigidity.md) | [Invariant chart subset](../roadmap/local-tests/chart-reduction.md) |
| `Pardon2013` Intro p. 1; `Lee1997`; `Gleason1952`, `MontgomeryZippin1952`, `Yamabe1953a`, `Yamabe1953b`, `MontgomeryZippin1955` | Hilbert--Smith reduction to $\Zp$ | [Classical reduction](../roadmap/background/classical-reduction.md) | [Hilbert--Smith conjecture](../roadmap/main-theorem/hilbert-smith-conjecture.md) |
| `KashiwaraSchapira1990` Ch. III; `SchapiraNotes` Thm 11.4.2, Props 11.4.3-11.4.4, 11.4.6(b), §11.7 | Dualizing complex, trace, internal duality | [Verdier duality formalism](../roadmap/background/verdier-duality.md) | [Test duality](../roadmap/sheaf-categories/test-duality.md), [pushforward](../roadmap/sheaf-categories/test-pushforward.md), [interval products](../roadmap/sheaf-categories/interval-products.md) |
| `SchapiraNotes` Thms 11.3.5-11.3.6, Cor 11.3.11, Eq. 11.3.1 | Base change, projection, Kunneth | [Sheaf pushforward toolkit](../roadmap/background/sheaf-pushforward.md) | [Test duality](../roadmap/sheaf-categories/test-duality.md), [pushforward](../roadmap/sheaf-categories/test-pushforward.md), [interval products](../roadmap/sheaf-categories/interval-products.md) |
| `SchapiraNotes` Def 11.3.1, Rem 11.3.3, Lemma 11.7.1, Props 11.2.4-11.2.5, 11.2.8 | c-soft dimension, soft resolutions | [Sheaf cohomology bounds](../roadmap/background/sheaf-cohomology-bounds.md) | [Test categories](../roadmap/sheaf-categories/test-categories.md), [character coproducts](../roadmap/character-classes/character-coproduct.md) |
| `BalmerWalter2002` Thm 2.1; `Balmer2000` | Witt localization sequence | [Balmer--Walter localization](../roadmap/background/balmer-walter.md) | [Witt localization](../roadmap/localization/witt-localization.md) |
| `Balmer2000` §1 | Duality, symmetric forms, orthogonal sums | [Symmetric forms and orthogonal sums](../roadmap/background/symmetric-forms.md) | [Dense doubling](../roadmap/localization/dense-doubling.md), [symmetric cone](../roadmap/sheaf-categories/symmetric-cone.md) |
| `Balmer2000` §1 | Involutive duality, transpose | [Transpose involution and orthogonal sums](../roadmap/background/transpose-involution.md) | [Dense doubling](../roadmap/localization/dense-doubling.md), [symmetric cone](../roadmap/sheaf-categories/symmetric-cone.md) |
| `Balmer2000` §1 | Symmetrization by averaging | [Symmetrization by averaging](../roadmap/background/symmetrization.md) | [Symmetric cone](../roadmap/sheaf-categories/symmetric-cone.md) |
| `Serre1951` Ch. V §3 Prop 3; `Serre1953` Ch. V §1 Cor 2 | Odd-sphere homotopy, degree maps | [Serre odd-sphere maps](../roadmap/background/serre-maps.md) | [Odd-sphere nullhomotopy](../roadmap/local-tests/odd-sphere-null.md) |
| `Hardt1980`; `Coste2000` Thm 4.1; `HardtLambrechtsTurchinVolic2011` §2.1 | Semialgebraic triviality, triangulation | [Hardt triviality](../roadmap/background/hardt-triviality.md) | [Generic signature](../roadmap/sphere-lattice/generic-signature.md) |
| `Hatcher2002` Thm 2C.1, Prop 2.30 | Simplicial approximation, local degree | [Hatcher degree facts](../roadmap/background/hatcher-facts.md) | [Degree action](../roadmap/sphere-lattice/degree-action.md) |
| `BergfalkLupiniPanagiotopoulos2024`; `StacksCechComparison` 20.16.2, 20.15.1; `EilenbergSteenrod1952` Ch. IX | Cech--sheaf comparison | [Cech comparison](../roadmap/background/cech-comparison.md) | [Orbit pullback](../roadmap/local-tests/orbit-injectivity.md), [odd-sphere nullhomotopy](../roadmap/local-tests/odd-sphere-null.md) |
| `StacksProperBaseChange` 20.18.1-20.18.2; `StacksDerivedSums` 13.33.5; `StacksDerivedCategories` 13.11.3, 13.11.6 | Base change, derived sums | [Stacks derived facts](../roadmap/background/stacks-derived.md) | [Orbit pullback](../roadmap/local-tests/orbit-injectivity.md), [character coproducts](../roadmap/character-classes/character-coproduct.md) |
| Standard; sketched in §5 lines 61-66 | Closed subgroups of $\Zp$ | [Closed subgroups of $\Zp$](../roadmap/background/padic-subgroups.md) | [Chart reduction](../roadmap/local-tests/chart-reduction.md), [finite sheets](../roadmap/local-tests/finite-sheets.md), [$p$-adic exclusion](../roadmap/main-theorem/padic-exclusion.md) |
| Standard Lie structure | Compact abelian Lie groups | [Compact abelian Lie groups](../roadmap/background/compact-abelian-lie.md) | [Almost-periodic flow](../roadmap/main-theorem/almost-periodic-flow.md) |

## Survey and antecedent references (no articles)

These appear in the introduction for context or as alternative
approaches; the proof does not depend on them:

- `Hilbert1902`, `BochnerMontgomery1946`, `RepovsScepin1997`,
  `Maleshich1997`, `Martin1999`, `Mj2012`, `Yang1960`,
  `BredonRaymondWilliams1961`, `Raymond1961`, `Shelukhin2024`.
- `Verdier1966` (superseded by Kashiwara--Schapira in the paper).
- `Woolf2008`, `RanickiWeiss2010` (antecedents; the paper proves
  its own versions).
- `HornbostelSchlichting2004` Thm A.2 (the paper gives a direct
  proof instead).
- `DranishnikovFerryWeinberger2003` (same telescope argument).
- `Pardon2013` Thm 1.5, §4.1 (prior case and reduction the paper
  re-proves as needed); Conj. 1.4 is proved as
  [Almost-periodic flow](../roadmap/main-theorem/almost-periodic-flow.md).

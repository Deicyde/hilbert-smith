# HS paper source map

The adopted source is A. Dabrowski's AI agents, *Integral tail
signatures and the Hilbert–Smith conjecture*, October 8, 2026: the HS
paper, whose proof the [two-routes chapter](../roadmap/two-routes/README.md)
calls HS_proof.

- Adopted revision: `5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862` of adbrw/HS_proof.
- [LaTeX source at adopted revision](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex) (`HSproof.tex`, 1504 lines).
- [Paper PDF at adopted revision](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.pdf).

The repository carries no license, so this map records only line spans,
numbers, labels and titles, and reproduces no sentence of the paper.
Line spans are 1-based within `HSproof.tex` and link to the adopted
revision. Labels are the paper's `\label` keys. Theorems, propositions,
lemmas, corollaries and definitions share one counter per section, and
equations are numbered per section. Names in parentheses are the
paper's own; the other descriptions are this map's.

## Section 1: Introduction (`sec:introduction`, lines 76-150)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Theorem 1.1 ($p$-adic exclusion) | `thm:main` | [85-88](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L88) | [What each paper proves](../roadmap/two-routes/statements.md), [HS_proof's route from its inputs](../roadmap/two-routes/hs-route.md) |
| Corollary 1.2 (Hilbert–Smith) | `cor:HS` | [90-94](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L90-L94) | [What each paper proves](../roadmap/two-routes/statements.md), [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md) |
| Standing conventions on manifolds; the standard reduction | (none) | [96-101](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L96-L101) | [What each paper proves](../roadmap/two-routes/statements.md), [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md) |
| Outline of the obstruction | (none) | [103-126](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L103-L126) | [Chapter page](../roadmap/two-routes/README.md) |
| (Conventions), unnumbered subsection | (none) | [128-150](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L128-L150) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md), [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |

## Section 2: Asymptotic categories and support (`alg:categories`, lines 152-228)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Definition 2.1: the asymptotic category | `alg:category` | [157-167](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L157-L167) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |
| (2.1)-(2.2): propagation and its bounds | `alg:propagation`, `alg:propbounds` | [162-176](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L162-L176) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |
| (2.3): supported subcategories and the exterior quotient | `alg:exterior` | [177-187](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L177-L187) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |
| Lemma 2.2 (Support calculus), with (2.4) | `alg:filtration`, `alg:excision`, `alg:relabel`, `alg:separation`, `alg:excision-equivalence` | [189-225](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L189-L225) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |

## Section 3: Integer signatures and tails (`alg:tails`, lines 230-315)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (3.1): coefficient-of-identity trace | `alg:trace` | [232-238](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L232-L238) | [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md), [Chapter page](../roadmap/two-routes/README.md) |
| (3.2): signature representation | `alg:signature` | [238-257](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L238-L257) | [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |
| Lemma 3.1 (Cyclic arithmetic) | `alg:cyclotomic` | [259-269](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L259-L269) | [Why the symmetry forces divisibility](../roadmap/two-routes/symmetry-forces.md) |
| (3.3): sequences modulo finite support | `alg:Vcategory` | [271-277](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L271-L277) | [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |
| Proposition 3.2 (Tail extraction), with (3.4) | `alg:extraction`, `alg:tail-isomorphism` | [279-307](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L279-L307) | [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |
| (3.5): the signature tail | `alg:signature-tail` | [309-315](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L309-L315) | [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |

## Section 4: Divisibility over a free $C_p$-space (`alg:obstruction`, lines 317-380)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (4.1): the operator $\nu$ | `alg:nu` | [320-327](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L320-L327) | [Why the symmetry forces divisibility](../roadmap/two-routes/symmetry-forces.md) |
| Lemma 4.1 (Local triviality), with (4.2) | `alg:localtrivial`, `alg:localisometry` | [329-348](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L329-L348) | [Why the symmetry forces divisibility](../roadmap/two-routes/symmetry-forces.md), [Free sheets, and putting the test over them](../roadmap/two-routes/free-sheets.md) |
| Lemma 4.2 (Nilpotence), with its fixed cover | `alg:nilpotence` | [350-365](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L350-L365) | [Why the symmetry forces divisibility](../roadmap/two-routes/symmetry-forces.md) |
| Theorem 4.3 (Integer tail divisibility), with (4.3) | `alg:divisibility`, `alg:factorannihilation` | [367-380](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L367-L380) | [Why the symmetry forces divisibility](../roadmap/two-routes/symmetry-forces.md), [The collision](../roadmap/two-routes/contradiction.md) |

## Section 5: Rational Poincaré corners (`alg:corners`, lines 382-511)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Section 5.1 (Signs and rational structures), with (5.1)-(5.2) | `alg:qmodel`, `alg:dualconvention`, `alg:qgroups` | [384-414](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L384-L414) | [Chapter page](../roadmap/two-routes/README.md), [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |
| Section 5.2 (Compatible idempotents and normalization), (5.3)-(5.5): homotopy action and graph idempotent | `alg:grouprelations`, `alg:graphidempotent`, `alg:graphrelations` | [416-436](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L416-L436) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Lemma 5.1 (Compatible splitting), with (5.6)-(5.7) | `alg:corner`, `alg:split`, `alg:cornerform` | [438-485](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L438-L485) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Lemma 5.2 (Scalar normalization), with (5.8)-(5.9) | `alg:normalization`, `alg:uvrelations`, `alg:scalarisometry` | [487-511](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L487-L511) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |

## Section 6: Localization boundaries (`sec:localization`, lines 513-575)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (6.1): ordinary localization boundary | `eq:ordinary-boundary` | [514-520](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L514-L520) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |
| Proposition 6.1: exterior boundary, with (6.2)-(6.3) | `prop:exterior-boundary`, `eq:exterior-boundary`, `eq:exterior-excision` | [522-552](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L522-L552) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md), [Why the class is not zero](../roadmap/two-routes/normalization.md) |
| Lemma 6.2: boundary of a union of pairs, with (6.4) | `lem:union-boundary`, `eq:union-boundary` | [554-575](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L554-L575) | [Why the class is not zero](../roadmap/two-routes/normalization.md) |

## Section 7: Local chain carriers (`sec:carriers`, lines 577-753)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Lemma 7.1 (Finite acyclic carriers) | `lem:finite-acyclic-carrier` | [585-603](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L585-L603) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Corollary 7.2: propagation of carried maps | `cor:carrier-control` | [605-614](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L605-L614) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Lemma 7.3 (Filling on a fixed triangulation) | `lem:unchanged-target-filling` | [616-641](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L616-L641) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Lemma 7.4 (Relative dual-block carrier maps) | `lem:relative-block-carriers` | [643-695](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L643-L695) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Lemma 7.5 (Controlled cap–block comparison) | `lem:cap-block-comparison` | [697-729](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L697-L729) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Corollary 7.6 (A common simplicial diagonal) | `cor:common-diagonal-control` | [731-753](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L731-L753) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |

## Section 8: Geometric data and quotient representatives (`geo:fixed-data`, lines 755-846)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Invariant second-countable open submanifold (unnumbered) | (none) | [757-768](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L757-L768) | [Where second countability goes](../roadmap/two-routes/second-countability.md) |
| Lemma 8.1: a point with trivial stabilizer | `geo:free-point` | [770-780](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L770-L780) | [One chart and a small subgroup](../roadmap/two-routes/one-chart.md), [HS_proof's route from its inputs](../roadmap/two-routes/hs-route.md) |
| (8.1): the chart and the small subgroup $H$ | `geo:small-H` | [782-786](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L782-L786) | [One chart and a small subgroup](../roadmap/two-routes/one-chart.md) |
| (8.2)-(8.3): the coordinate average $F_0$ | `geo:average`, `geo:average-bounds` | [787-796](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L787-L796) | [An invariant degree-one map to a sphere](../roadmap/two-routes/averaged-test.md) |
| (8.4): the compact set $Z^+$ | `geo:Zplus` | [797-803](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L797-L803) | [Free sheets, and putting the test over them](../roadmap/two-routes/free-sheets.md) |
| (8.5)-(8.6): the pinched map $f$ and its degree | `geo:f`, `geo:pinch-homotopy` | [804-816](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L804-L816) | [An invariant degree-one map to a sphere](../roadmap/two-routes/averaged-test.md) |
| (8.7): the equivariant detector to $T$ | `geo:detector` | [818-830](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L818-L830) | [Free sheets, and putting the test over them](../roadmap/two-routes/free-sheets.md) |
| (8.8): buffer radii and the exterior | `geo:buffers` | [831-838](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L831-L838) | [Free sheets, and putting the test over them](../roadmap/two-routes/free-sheets.md), [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (8.9): the finite quotients $G_i$ | `geo:finite-quotients` | [839-846](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L839-L846) | [Free sheets, and putting the test over them](../roadmap/two-routes/free-sheets.md), [The collision](../roadmap/two-routes/contradiction.md) |

## Section 9: Common chain models (`geo:chain-models`, lines 848-977)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Lemma 9.1: chain models and chain approximations, with (9.1) | `geo:closed-models`, `geo:mu` | [850-878](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L850-L878) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (9.2)-(9.5): completed maps, product tracks, graph type, fundamental cycle | `geo:completed-map`, `geo:f-invariance`, `geo:raw-product-track`, `geo:fundamental-cycle` | [880-913](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L880-L913) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md), [Chapter page](../roadmap/two-routes/README.md) |
| Lemma 9.2: product homotopies, with (9.6) | `geo:product-homotopies`, `geo:product-equation` | [916-946](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L916-L946) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (9.7)-(9.8): isometry and adjoint homotopies | `geo:isometry-homotopy`, `geo:adjoint-homotopy` | [948-977](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L948-L977) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |

## Section 10: Compression and exterior control (`geo:compression`, lines 979-1100)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (10.1): compression data | `geo:compression-data` | [981-996](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L981-L996) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Lemma 10.1 (Exterior band), with (10.2) | `geo:band-factorization`, `geo:band` | [998-1026](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L998-L1026) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (10.3): compressed maps | `geo:compressed-maps` | [1028-1037](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1028-L1037) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Proposition 10.2: the compressed Poincaré complex, with (10.4)-(10.7) | `geo:compressed-realization`, `geo:compression-product`, `geo:compression-chain`, `geo:compression-relation`, `geo:compressed-orientation` | [1039-1100](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1039-L1100) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |

## Section 11: The graph corner and its scalar image (`sec:equivariant`, lines 1102-1146)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (11.1): sheet labels | `eq:sheet-labels` | [1104-1110](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1104-L1110) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (11.2)-(11.3): the graph idempotent in the exterior quotient | `eq:graph-idempotent`, `eq:controlled-idempotent` | [1111-1127](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1111-L1127) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (11.4)-(11.5): the normalized corner and its class | `eq:normalized-corner`, `eq:d-class` | [1128-1137](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1128-L1137) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| (11.6): the scalar image | `eq:scalar-image` | [1139-1146](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1139-L1146) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md), [Why the class is not zero](../roadmap/two-routes/normalization.md) |

## Section 12: Evaluation of the iterated boundary (`bd:scalar`, lines 1148-1324)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (12.1)-(12.2): the iterated boundary and its naturality | `bd:Delta`, `bd:naturality` | [1149-1172](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1149-L1172) | [Why the class is not zero](../roadmap/two-routes/normalization.md) |
| Lemma 12.1 (Controlled relative duality), with (12.3)-(12.4) | `bd:relative`, `bd:Psi`, `bd:cone-contraction` | [1174-1221](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1174-L1221) | [Why the class is not zero](../roadmap/two-routes/normalization.md) |
| Lemma 12.2 (Controlled unions), with (12.5) | `bd:union`, `bd:union-tensor` | [1223-1257](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1223-L1257) | [Why the class is not zero](../roadmap/two-routes/normalization.md) |
| Lemma 12.3 (Scalar control homotopies) | `bd:homotopy` | [1259-1287](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1259-L1287) | [Why the class is not zero](../roadmap/two-routes/normalization.md), [Chapter page](../roadmap/two-routes/README.md) |
| Proposition 12.4 (Boundary evaluation), with (12.6)-(12.7) | `bd:pinch-value`, `bd:CP2`, `bd:pinch-homotopy` | [1289-1324](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1289-L1324) | [Why the class is not zero](../roadmap/two-routes/normalization.md) |

## Section 13: The contradiction (`sec:contradiction`, lines 1326-1391)

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| Proposition 13.1 (Signature-one realization), with (13.1) | `prop:signature-one`, `eq:signature-one` | [1328-1350](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1328-L1350) | [Why the class is not zero](../roadmap/two-routes/normalization.md), [The collision](../roadmap/two-routes/contradiction.md) |
| Proof of Theorem 1.1: dimension 0 and boundary | (none) | [1352-1359](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1352-L1359) | [What each paper proves](../roadmap/two-routes/statements.md) |
| Proof of Theorem 1.1: the boundaryless case | (none) | [1361-1365](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1361-L1365) | [The collision](../roadmap/two-routes/contradiction.md) |
| Proof of Corollary 1.2: compact subgroups are Lie | (none) | [1367-1381](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1367-L1381) | [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md), [Where second countability goes](../roadmap/two-routes/second-countability.md) |
| Proof of Corollary 1.2: Gleason–Yamabe and no small subgroups | (none) | [1383-1391](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1383-L1391) | [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md) |

## After Section 13

| Result | Label | Lines | Two-routes page |
| --- | --- | --- | --- |
| (AI disclosure), unnumbered section | (none) | [1393-1400](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1393-L1400) | [Chapter page](../roadmap/two-routes/README.md) |
| Bibliography entry [BS01] | `BS01` | [1404-1408](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1404-L1408) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md) |
| Bibliography entry [CP95] | `CP95` | [1410-1414](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1410-L1414) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md) |
| Bibliography entry [Gle52] | `Gle52` | [1416-1420](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1416-L1420) | [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md) |
| Bibliography entry [Hat02] | `Hat02` | [1422-1425](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1422-L1425) | [Turning the action into classes](../roadmap/two-routes/classes-from-action.md), [Why the class is not zero](../roadmap/two-routes/normalization.md) |
| Bibliography entry [Pa19] | `Pa19` | [1439-1445](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1439-L1445) | [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md) |
| Bibliography entry [Ran92] | `Ran92` | [1465-1469](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1465-L1469) | [The group that carries the invariant](../roadmap/two-routes/the-invariant.md), [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |
| Bibliography entry [Rob75] | `Rob75` | [1477-1481](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1477-L1481) | [One chart and a small subgroup](../roadmap/two-routes/one-chart.md) |
| Bibliography entry [Wei13] | `Wei13` | [1489-1493](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1489-L1493) | [Reading an integer, fixed in advance](../roadmap/two-routes/integrality.md) |
| Bibliography entry [Yam53] | `Yam53` | [1495-1499](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L1495-L1499) | [From locally compact groups to $\mathbb{Z}_p$](../roadmap/two-routes/groups-to-zp.md) |

## Reading notes

- The two-routes page given for each row follows the chapter's stage
  pairing; the chapter page lists the steps that only one proof has.
- HS_proof's Lean library, `HSFormal`, in the same repository, names
  some results by an earlier numbering of the paper: its `theorem_6_3`
  is Theorem 4.3 and its `lemma_6_2` is Lemma 4.2.
- The paper states Theorem 1.1 and Corollary 1.2 without second
  countability, and reduces to it at the start of Section 8 and in the
  proof of Corollary 1.2; its AI disclosure names the Lean formalization,
  which assumes second countability.

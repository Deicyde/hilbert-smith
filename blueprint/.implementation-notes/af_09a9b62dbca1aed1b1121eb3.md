# Note: Dense doubling

Verified at the pinned Mathlib rev (v4.34.1, local checkout).

Gap: no triangular Witt groups. A full-tree search finds no `W_r`,
no Witt groups of triangulated categories, and no Balmer--Walter
localization sequence. `Mathlib/CategoryTheory/Triangulated/`
exists (Basic, Functor, HomologicalFunctor, ...), but the entire
Witt layer above it is absent: symmetric forms, neutral forms,
hyperbolic planes, doubling identities.

Formalizing this leaf requires defining triangular Witt theory
from scratch (forms, metabolic objects, the `D(q)` doubling with
its lagrangian verification) before the leaf's two identities can
even be stated. Multi-pass epic; not feasible as a frontier pass.

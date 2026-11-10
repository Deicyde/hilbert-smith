---
article_id: af_6ac106b435d4584d7235e2a6
---

# Newman's theorem

Newman's theorem says that a periodic homeomorphism of a connected manifold cannot be the identity on part of the manifold without being the identity everywhere, and that one whose orbits are all small on a chart ball fixes that ball. The main text uses it in two forms. Both are open statements: the Lean states them now and proves them later.

The open-set form is used twice: for the good point, where a small subgroup acting on a saturated ball factors through a finite group, and in the group step, to pass from a fixed ball to a trivial element.

- [Newman's theorem: fixing an open set](newman-open-set.md)

The small-orbit form excludes elements of prime order near the identity of a group acting faithfully. Its constant depends on the manifold and the chart but not on the prime, and it needs no second countability, because it only looks at one chart ball.

- [Newman's theorem: small orbits](newman-small-orbits.md)

Remark (not formalized). The small-orbit form, with one constant for every prime and smallness required only on the closed chart ball, has not been checked against a published statement. If no reference is found, the group step can instead follow the HS paper's route, which proves that compact subgroups are Lie and then uses the structure theorem of Gleason and Yamabe. That route does not avoid a small-orbit statement: making a compact subgroup Lie classically excludes elements of prime order near the identity by Newman's theorem on orbit diameters. It would need Newman's theorem only in its published forms (for compact Lie groups, on second-countable manifolds, with the constant of the global orbit-diameter theorem); which forms suffice has not been checked.

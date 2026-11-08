---
article_id: af_5fc68ca649c338433c7954fc
declaration: theorem
origin: bridged
lean: HSBridge.hs_route_of_inputs
statement: formalized
proof: formalized
---

# HS_proof's route from its inputs

Let $\mathbb{L}$ be a lower $L$-theory, and assume Newman's theorem for
prime order. Then for every prime $p$, every $n \geq 0$ and every
connected, Hausdorff, second-countable topological $n$-manifold $M$
without boundary, every jointly continuous action of $\mathbb{Z}_p$ on
$M$ has nonzero kernel: some nonzero $p$-adic integer acts as the
identity.

A *lower $L$-theory* assigns to every small $\mathbb{Q}$-linear additive
category $\mathcal{A}$ with a strict involution and unitary biproducts,
and to every integer $n$, an abelian group $L_n(\mathcal{A})$, with:

- functoriality along duality-preserving functors, unitarily isomorphic
  functors inducing the same map and finite unitary sums inducing the
  sum;
- natural maps from the projective $L$-groups (taken to be zero in
  negative degrees) that are bijective, in nonnegative degrees, on
  finite-support sums of the categories of free $\mathbb{Q}[G_i]$-modules
  with $G_i$ finite;
- a natural long exact localization sequence for every Karoubi
  filtration;
- a boundary map that sends the class of a Poincaré pair with boundary
  in the filtering subcategory to the class of that boundary, up to a
  universal sign.

*Newman's theorem for prime order* says that for every connected,
second-countable topological manifold $N$ without boundary with a
compatible metric, and every nonempty open $U \subseteq N$, there is
$\varepsilon > 0$ such that every homeomorphism $f$ of $N$ with
$f^q = \mathrm{id}$ for a prime $q$, all of whose iterates move each
point of $U$ by less than $\varepsilon$, is the identity. It is the
displacement form of Newman's theorem.
Applied to a homeomorphism of prime order that is the identity on $U$,
it gives the form used in [One chart and a small subgroup](one-chart.md)
for these manifolds: a periodic homeomorphism that is the identity on a
nonempty open set is the identity (pass to a power of prime order). The
form for compact Lie groups in
[From locally compact groups to $\mathbb{Z}_p$](groups-to-zp.md) is a
different statement.

This is Theorem 1.1 of the HS paper for second-countable manifolds
without boundary
([lines 85-88](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L85-L88)),
with its proof reduced to two inputs. The first stands for the ultimate
lower quadratic $L$-theory that the paper cites, with the properties it
lists
([lines 140-150](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L140-L150))
and invariance under unitary isomorphism; the bijectivity is the step
where the paper's proof of Proposition 3.2 uses vanishing negative
$K$-theory
([lines 290-298](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L290-L298)).
The second replaces Roberts' theorem on pointwise finite families of
maps, which the paper cites to find a point with trivial stabilizer
([lines 774-779](https://github.com/adbrw/HS_proof/blob/5dee3407a627f35a2cdeb0a34ac9e0f1ee98f862/HSproof.tex#L774-L779)):
Newman's theorem for prime order implies that a pointwise periodic
homeomorphism of a connected manifold without boundary is periodic.
The ultimate lower $L$-theory is a lower $L$-theory in this sense, and
Newman's theorem for prime order holds, so the conclusion also holds
outright; this statement keeps the two inputs visible as hypotheses.

*Proof sketch.* The proof follows the stages of the paper's proof of
Theorem 1.1 in the table on the [chapter page](README.md): a free point
and one chart, the pinched coordinate average $f = s_\rho F_0$, the free
$C_p$-sphere $T$ with its detector, the equivariant class over $T$ and
its scalar image, divisibility of the signature tail by $p$, and the
boundary evaluation. It departs from the paper in several places. The
free point comes from Montgomery's theorem, that a pointwise periodic
homeomorphism of a connected manifold is periodic, which follows from
Newman's theorem for prime order. Cubical chain models replace
triangulations. Since the pinch is homotopic to the
identity, the germ is evaluated at the identity, cutting along the faces
of a cube. The contradiction is drawn on the scalar side, from a tail
that is eventually $\pm 1$ and also divisible by $p$. The two inputs
enter at the free point and wherever the $L$-groups are used.

## Sources

- [HS paper source map](../../sources/hs-paper.md)

## Depends on

This node has no prerequisites.

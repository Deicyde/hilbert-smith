---
article_id: af_9afb26ed0ad9890d5b116dfd
declaration: theorem
origin: cited
---

# Lifting

Let $\mathcal U\subset\mathcal A$ be an [involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md). Let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ be a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md) with image $qV=(qD,q_\%\delta\phi)$ ([Image of a pair with boundary in Kar U](image-pair.md)), and let $W=(g:qD\to W_\bullet,\delta\psi,q_\%\delta\phi)$ be a strict $(k+1)$-dimensional Poincaré pair in $\mathrm{Dec}(\mathcal A/\mathcal U)$ with boundary $qV$. Then there are

(a) a strict $k$-dimensional Poincaré pair $R=(P\to R_\bullet,\rho,-\pi)$ in $\mathrm{Kar}\,\mathcal U$ with boundary $(P,-\pi)$, and

(b) a strict $(k+1)$-dimensional Poincaré pair $E=(e:D\cup_PR\to E_\bullet,\delta\epsilon,\Phi)$ in $\mathrm{Kar}\,\mathcal A$ whose boundary is the [closed union](closed-union.md) $(D\cup_PR,\Phi)$,

such that

(c) $[W\cup(-E^\sharp)]=0$ in $L^{\mathrm{im}}_{k+1}(\mathcal A/\mathcal U)$.

Here $p:q(D\cup_PR)\to qD$ is the isomorphism of [The closed union becomes the image of the pair](union-image.md), and $E^\sharp=(qe\circ p^{-1}:qD\to qE_\bullet,\ q_\%\delta\epsilon,\ q_\%\delta\phi)$, a strict pair in $\mathrm{Dec}(\mathcal A/\mathcal U)$ by [Duality functors carry pairs to pairs](functor-pair.md) and [Pair transport](../../base/pairs/pair-transport.md). $W\cup(-E^\sharp)$ is the [algebraic union](../../base/pairs/algebraic-union.md) with $V_A=W$ and $V_B$ the negation of $E^\sharp$, its boundary map precomposed with the canonical isomorphism $Z\oplus qD\to qD$ for the zero complex $Z$ ([Pair transport](../../base/pairs/pair-transport.md)). It is a strict $(k+1)$-dimensional symmetric Poincaré complex in $\mathrm{Dec}(\mathcal A/\mathcal U)$ by [Closed gluing](../../base/pairs/gluing-closed.md).

**Remark (not formalized).** *Status.* This is an open statement. With $V$ the zero $\mathcal U$-pair (all chain objects zero objects) it gives [Lifting closed complexes](lift-to-pair-closed.md). Parts (a) and (b) alone say that a $\mathcal U$-pair whose image bounds in $\mathrm{Dec}(\mathcal A/\mathcal U)$ is null-cobordant relative to $\mathcal U$. Together the two cases say that the comparison map from the relative L-groups of $\mathcal U\subset\mathcal A$ to $L^{\mathrm{im}}$ is bijective, the form in which the localization theorem is usually proved [U]. This paper does not define relative L-groups.

*Planned route.* (1) [Stabilization](../decorations/stabilization.md) makes every chain object of $W_\bullet$ isomorphic to some $qQ_r$ with $Q_r$ in $\mathrm{Kar}\,\mathcal A$. (2) Lift the differentials of $W_\bullet$ and the map $g$, keeping $D$ on the boundary, by [The completed quotient is full](../../base/categories/karoubi-quotient-full.md). The defects, such as the lifted $d^2$, factor through $\mathrm{Kar}\,\mathcal U$ by [Kernel of the completed quotient](../../base/categories/karoubi-quotient-kernel.md). Remove the lifted $d^2$ by downward induction on the degree $s$: the composite $Q_{s+2}\to Q_s$ factors through $\mathcal U$, so split off a $\mathcal U$-summand of $Q_s$ through which it factors and project onto the complement. This changes $qQ_s$ only up to isomorphism and leaves the composites into higher degrees unchanged. (3) Lift $\delta\psi$ and average the lift with its transpose, which removes the symmetry defect over $\mathbb Q$. (4) Form the algebraic boundary of the lifted, non-Poincaré pair [U: Ranicki 1980 I, Prop 3.4]. Its new boundary part is contractible modulo $\mathcal U$. Replace that part by a homotopy equivalent complex in $\mathrm{Kar}\,\mathcal U$ and move the pair along the equivalence by [Transport along a homotopy equivalence](../../base/pairs/pair-transport-equivalence.md). (5) Read off $R$ as the part over $\mathrm{Kar}\,\mathcal U$ and $E$ as the lifted pair. Part (c) holds because $qE$ differs from $W$ only by the stabilizer of step (1) and by summands that vanish modulo $\mathcal U$.

*Known gaps.* (i) Step (2) needs $\mathcal U$-decompositions of the $Q_s$. The filtration provides them for objects of $\mathcal A$ but not for objects of $\mathrm{Kar}\,\mathcal A$, because $\mathrm{Kar}\,\mathcal U\subset\mathrm{Kar}\,\mathcal A$ need not be a Karoubi filtration ([Completion of a subcategory](../../base/categories/kar-subcategory.md), Remark (b)). (ii) The chain-map defect $d\,\delta\tilde\psi-(-1)^r\delta\tilde\psi\,d^*$ of the lifted structure, measured against the boundary structure, also factors through $\mathrm{Kar}\,\mathcal U$. No derivation that removes it is written; Carlsson and Pedersen treat it [U]. (iii) The step "contractible modulo $\mathcal U$ implies homotopy equivalent to a complex in $\mathrm{Kar}\,\mathcal U$" in (4) is unproved, for the same reason as (i). (iv) The base chapter has no triads, so the bookkeeping of the two boundary pieces of $E$ in (5) must go through the algebraic union, and it has not been written.

## Sources

- [Carlsson-Pedersen 1995, Section 4](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- [Ranicki 1980 I, Prop 3.4, algebraic boundary](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the relative, class-level form, chosen as the weakest statement the localization proofs use

## Depends on

- [U-pairs](u-pair.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [Closing a pair by a null-cobordism of its boundary](closed-union.md)
- [The closed union becomes the image of the pair](union-image.md)
- [Duality functors carry pairs to pairs](functor-pair.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Algebraic union](../../base/pairs/algebraic-union.md)
- [Closed gluing](../../base/pairs/gluing-closed.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)

## Proof depends on

- [Stabilization](../decorations/stabilization.md)
- [The completed quotient is full](../../base/categories/karoubi-quotient-full.md)
- [Kernel of the completed quotient](../../base/categories/karoubi-quotient-kernel.md)
- [Transport of pairs along homotopy equivalences](../../base/pairs/pair-transport-equivalence.md)
- [Completion of a subcategory](../../base/categories/kar-subcategory.md)

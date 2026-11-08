---
article_id: af_5eed727491112074afc00171
declaration: theorem
origin: bridged
lean: HSBridge.oai_route_noSC
statement: formalized
proof: formalized
---

# OpenAI's route without second countability

Let OpenAI's interface be given, together with local inputs for it.
Then for every prime $p$, every $n \geq 0$ and every connected
Hausdorff topological $n$-manifold $M$ without boundary, with no
countability assumption, every jointly continuous action of
$\mathbb{Z}_p$ on $M$ has nonzero kernel: some nonzero $p$-adic integer
acts as the identity.

*OpenAI's interface* supplies, for every odd $d = 2j + 3$, fixed
self-maps $\delta_r$ of $S^d$ ($r \geq 2$) and the invariant as
Sections 5 and 6 use it:

- a class of test spaces containing $S^d$ and the close-pair space
  $C_d$, and abelian groups $E_d(X)$ with pushforwards, functorial on
  test spaces and equal for homotopic maps;
- a class $u_d \in E_d(S^d)$ of infinite order and an integer $L_d > 0$
  such that $L_d x$ is rationally an integer multiple of $u_d$ for every
  $x \in E_d(S^d)$;
- degree maps: $\delta_r$ acts rationally as multiplication by $r$ on
  $u_d$;
- quotient categories $\mathcal{Q}_U(X)$ with duality, Witt groups and
  pushforwards, and integral isomorphisms
  $\ell_U \colon E_d(X) \to W_d(\mathcal{Q}_U(X))$ for nonempty
  contractible open $U$ in a test space, natural in $X$;
- for every local action and admissible test $t$: test forms
  $(A_t, \alpha_t)$ whose classes are $2(f_t)_* u_d$ through $\ell_U$,
  and character projectors $e_i$ with $e_i^2 = e_i$, $e_ie_j = 0$ for
  $i \neq j$ and $\sum_i e_i = 1$, self-adjoint when the action
  preserves orientation (every element's local maps homotopic to those
  of the identity), carried to one another by pushforward along maps of
  tests, and conjugated from $e_i$ to $e_{i-1}$ by an isometry when the
  test is constant off a sheet region.

*Local inputs* for it say that for every odd $d = 2j + 3$, if a compact
metrizable space $X$ carries a continuous action of $\mathbb{Z}_p$ with
orbit map $q \colon X \to Y$ (a quotient map whose fibres are the
orbits), both spaces lying in the lowest universe, $F \subseteq Y$ is
closed, and $v \colon F \to S^d$ becomes nullhomotopic when composed
with $q$ on $q^{-1}(F)$, then
$\delta_{s+1} \circ \cdots \circ \delta_2 \circ v$ is nullhomotopic for
some $s \geq 0$; that composite of degree maps acts rationally as
multiplication by $(s+1)!$. The formal statement covers manifolds in
every universe.

This is Theorem 1.2 of the preprint without second countability and
without its finite-quotient clause, with $n = 0$ allowed
([Theorem 1.2](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/01-introduction.tex#L30-L35)).
The interface collects what Sections 5 and 6 use of Sections 2 to 4, of
the test forms, of Lemmas 6.1 and 6.2, and of the identifications inside
Propositions 6.5 and 6.7. The local inputs are Lemmas 5.4 and 5.5,
composed as in the proof of Proposition 5.8
([lines 506-512](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L506-L512)).
Newman's theorem, which Proposition 5.1 uses
([lines 24-29](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/05-local-tests.tex#L24-L29)),
is not a hypothesis: its proof is taken from HS_proof, and nothing else
from HS_proof is used. No model of the interface or of the local inputs
exists yet, so this is a conditional theorem; the chapter page explains
[how to read it](README.md).

*Proof sketch.* Suppose the action is faithful. Proposition 5.1, which
needs only Newman's theorem, gives a faithful action of an open subgroup
on a connected invariant open subset $O$ of $\mathbb{R}^n$, and an
open subgroup of it preserves orientation. Stabilize to
$W = O \times \mathbb{R}^{d-n}$ for an odd $d > n$ with $d \geq 3$;
Lemma 5.3 gives the averaged test; sliding the pinch into the region,
then Proposition 5.8, move a positive-degree multiple of it into each
sheet region of Lemma 5.6; and Theorem 6.8 turns the equal character
classes into the contradiction $m \mid 4L_d$ with $m > 4L_d$
([proof of Theorem 6.8](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L445-L500)). The
[proof of Theorem 1.2](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026/build/sections/06-character-classes.tex#L502-L516)
assembles these steps.

## Sources

- [OpenAI preprint source map](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

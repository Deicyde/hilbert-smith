---
article_id: af_9dd9d33528a95dd654a0aa38
declaration: theorem
origin: cited
---

# Homotopy invariance

If $h : I \times X \to Y$ is a continuous homotopy of maps of test
spaces, its endpoint maps induce equal homomorphisms
$h_{0*} = h_{1*} : E_r(X) \to E_r(Y)$ for every $r \in \Z$. The same
holds for $W_r(\Pcat(-))$ under allowed semialgebraic homotopies. In
particular, homotopy equivalences induce isomorphisms, and a
nonempty contractible test space has the Witt groups of a point.

*Proof sketch.* The endpoint relation plus rescaling by an inverse
square root (either sign of $c$) gives
$(i_0)_* = (i_1)_*$ on the cylinder; pushing along $h$ identifies
$h_{0*}$ and $h_{1*}$. Properness of the homotopy is unnecessary
since all objects have compact support. The $\Pcat$ case uses the
same relation with semialgebraic data.

## Sources

- [Preprint source map: `thm:homotopy`](../../sources/preprint.md)

## Depends on

- [Test categories](test-categories.md)
- [Direct images and open extension](test-pushforward.md)

## Proof depends on

- [Two endpoint forms](endpoint-forms.md)
- [Direct images and open extension](test-pushforward.md)

---
article_id: af_369dbfd885cdb7c192d717dd
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.trackModulus
---
# Modulus of the track family

For real $t$ put
$$\omega(t)=t+\sup\{d_\infty(Lx,Lx'):L\in\mathcal F,\ x,x'\in\mathbb T^n,\ d_\infty(x,x')\le t\},$$
the supremum of the [track oscillation](maps/track-oscillation.md) for the [track family](maps/track-family.md) $\mathcal F$. The supremum is finite ([the track oscillation is bounded](maps/track-oscillation-bounded.md)). For $t<0$ the set is empty, and its supremum is read as $0$.

## Sources
- HS paper, Section 9 (a common modulus for the completed maps and their tracks). New: the explicit formula.
## Depends on
- [Track oscillation](maps/track-oscillation.md), [the torus](../grid/torus.md)

## Proof depends on

- [The track oscillation is bounded](maps/track-oscillation-bounded.md)

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
with $\mathcal F$ the family of [track maps](track-map.md). The supremum is finite, since $d_\infty\le2$ on $\mathbb T^n$ ([diameter](../torus/dist-le-two.md)). For $t<0$ the set is empty, and its supremum is read as $0$.

## Sources
- HS paper, Section 9 (a common modulus for the completed maps and their tracks). New: the explicit formula.
## Depends on
- [Track maps](track-map.md), [the torus](../grid/torus.md)

## Proof depends on

- [The torus has diameter at most two](../torus/dist-le-two.md)

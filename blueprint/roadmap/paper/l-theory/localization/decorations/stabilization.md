---
article_id: af_af2d374484faaf3fc2a64ea8
declaration: lemma
origin: background
---

# Stabilization

Let $\mathcal U\subset\mathcal A$ be as in [Decorated objects](decorated-object.md), let $n\ge1$, and let $(f:C\to W,\delta\phi,\phi)$ be a strict $n$-dimensional Poincaré pair in $\mathrm{Dec}(\mathcal A/\mathcal U)$. Then there is a contractible complex $E$, whose chain objects are of the form $qX$ with $X$ in $\mathcal A$ and are zero objects outside $[0,n]$, such that each chain object of $W\oplus E$ is isomorphic to $qQ$ for some $Q$ in $\mathrm{Kar}\,\mathcal A$, and $((f,0):C\to W\oplus E,\ \delta\phi\oplus0,\ \phi)$ is a strict $n$-dimensional Poincaré pair in $\mathrm{Dec}(\mathcal A/\mathcal U)$.

*Proof sketch.* (1) For each $r\in[0,n]$, $W_r$ is decorated: $[W_r]=[qQ'_r]$ for some $Q'_r$ in $\mathrm{Kar}\,\mathcal A$. [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md) gives an object $X_r$ of $\mathcal A/\mathcal U$, that is, an object of $\mathcal A$, with $W_r\oplus qX_r\cong qQ'_r\oplus qX_r\cong qQ_r$, where $Q_r=Q'_r\oplus X_r$. (2) Let $E^{(r)}$ be $qX_r$ in degrees $r$ and $r+1$, joined by the identity, for $r<n$, and in degrees $n-1$ and $n$ for $r=n$. Put $E=\bigoplus_rE^{(r)}$. It is contractible, the contraction being the identity in the other direction. (3) $W_r\oplus E_r$ is $W_r\oplus qX_r$ plus further summands $qX_s$, hence isomorphic to $q$ of $Q_r$ plus the corresponding $X_s$. All these objects are decorated. (4) $\delta\phi\oplus0$ is $T$-invariant, and $\partial(\delta\phi\oplus0)=f_\%\phi\oplus0=(f,0)_\%\phi$. (5) After reordering summands, $\mathcal C((f,0))=\mathcal C(f)\oplus E$ and the [pair map](../../base/pairs/pair-map.md) is $\psi\oplus0$, with $0:E^{n-*}\to E$. $E^{n-*}$ is contractible by [Duals of homotopy equivalences](../../base/complexes/dual-homotopy-equivalence.md) applied to $E\to0$. A map between contractible complexes has contractible cone ([Twisted sums of contractible complexes](../../base/complexes/split-extension-contractible.md)), so it is an equivalence by the [Cone criterion](../../base/complexes/cone-criterion.md). Conclude with [Sums of equivalences](../../base/complexes/sum-equivalence.md).

## Sources

- New: adding contractible complexes with zero structure, from equality in $K_0$

## Depends on

- [Decorated objects](decorated-object.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)

## Proof depends on

- [Equality in $K_0$](../../bounded/categories/k-zero-stable-equality.md)
- [Pair map](../../base/pairs/pair-map.md)
- [Duals of homotopy equivalences](../../base/complexes/dual-homotopy-equivalence.md)
- [Twisted sums of contractible complexes](../../base/complexes/split-extension-contractible.md)
- [Cone criterion](../../base/complexes/cone-criterion.md)
- [Sums of equivalences](../../base/complexes/sum-equivalence.md)

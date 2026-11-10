---
article_id: af_05ca3db7c60a579317fcecf1
declaration: lemma
origin: bridged
---

# Homotopy-isometric complexes are cobordant

Let $\mathcal P$ be a class of objects of a duality category $\mathcal B$ closed under finite sums and duals. Let $(C,\phi)$ and $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in $\mathcal B$ whose chain objects lie in $\mathcal P$, let $h:C\to C'$ be a chain homotopy equivalence, and let $\chi\in M(C')_{k+1}$ satisfy $\partial\chi=h_\%\phi-\phi'$. Put $\chi'=(\chi+T\chi)/2$. Then $((h,1):C\oplus C'\to C',\ \chi',\ \phi\oplus(-\phi'))$ is a strict $(k+1)$-dimensional Poincaré pair whose chain objects lie in $\mathcal P$. Its boundary is $(C\oplus C',\phi\oplus(-\phi'))$, so it is a [cobordism](cobordism.md) from $(C,\phi)$ to $(C',\phi')$.

*Proof sketch.* (1) $T\chi'=\chi'$ and $\partial\chi'=\partial\chi$, since $T\partial=\partial T$, $T^2=1$, $g_\%T=Tg_\%$, and the right side is $T$-invariant. (2) $\partial\chi'=(h,1)_\%(\phi\oplus(-\phi'))$, and $(C\oplus C',\phi\oplus(-\phi'))$ is Poincaré by [Sums of equivalences](../complexes/sum-equivalence.md). $C'_r$ is a zero object outside $[0,k]\subset[0,k+1]$. The chain objects are $C'_r$ and $C_r\oplus C'_r$, which lie in $\mathcal P$. (3) The projection $\pi:\mathcal C((h,1))\to\Sigma C$, $(x,y,y')\mapsto y$, is [triangular](../complexes/triangular-map.md) from the [twisted sum](../complexes/twisted-sum.md) $\mathcal C(1_{C'})\oplus_\tau\Sigma C$ to $0\oplus\Sigma C$. $\mathcal C(1_{C'})$ is contractible via $(x,y')\mapsto(0,(-1)^rx)$. So $\pi$ is an equivalence by [Triangular equivalences](../complexes/triangular-equivalence.md). (4) $\pi\psi_r=(-1)^r\phi_{r-1}h^*$, so $\pi\psi=\Sigma(\phi_\natural h^{k-*})\circ\varepsilon$ with the isomorphism $\varepsilon_r=(-1)^r:C'^{k+1-*}\to\Sigma C'^{k-*}$. Here $\phi_\natural$ is an equivalence, $h^{k-*}$ is one by [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md), and $\Sigma$ preserves equivalences by [Shifts of homotopy equivalences](../complexes/shift-equivalence.md), so $\pi\psi$ is an equivalence. Hence $\psi$ is one, by two-out-of-three.

## Sources

- HS paper, Section 5 (symmetrizing a primitive)
- [Ranicki 1989, Def 3.10](../../../../../sources/paper/ranicki-1989.md) [U]

## Depends on

- [Cobordism](cobordism.md)
- [Strict Poincaré pair](poincare-pair.md)

## Proof depends on

- [T is an involution](../complexes/structure-involution-square.md)
- [Pushforward commutes with T](../complexes/structure-push-involution.md)
- [Sums of equivalences](../complexes/sum-equivalence.md)
- [Twisted sum](../complexes/twisted-sum.md)
- [Triangular map](../complexes/triangular-map.md)
- [Triangular equivalences](../complexes/triangular-equivalence.md)
- [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md)
- [Shifts of homotopy equivalences](../complexes/shift-equivalence.md)

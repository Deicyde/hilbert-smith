---
article_id: af_05ca3db7c60a579317fcecf1
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.cylinder_cobordism
proof: formalized
---

# Homotopy-isometric complexes are cobordant

Let $\mathcal P$ be a class of objects of a duality category $\mathcal B$ such that every direct sum (biproduct) of two objects of $\mathcal P$ lies in $\mathcal P$. Let $(C,\phi)$ and $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in $\mathcal B$ whose chain objects lie in $\mathcal P$, let $h:C\to C'$ be a chain homotopy equivalence, and let $\chi\in M(C')_{k+1}$ satisfy $\partial\chi=h_\%\phi-\phi'$. Put $\chi'=(\chi+T\chi)/2$. Then $((h,1):C\oplus C'\to C',\ \chi',\ \phi\oplus(-\phi'))$ is a strict $(k+1)$-dimensional Poincaré pair whose chain objects lie in $\mathcal P$. Its boundary is $(C\oplus C',\phi\oplus(-\phi'))$, so it is a [cobordism](cobordism.md) from $(C,\phi)$ to $(C',\phi')$.

*Proof sketch.* (1) $T\chi'=\chi'$ and $\partial\chi'=\partial\chi$, since $T\partial=\partial T$, $T^2=1$, $g_\%T=Tg_\%$, and the right side is $T$-invariant. (2) $\partial\chi'=(h,1)_\%(\phi\oplus(-\phi'))$, and $(C\oplus C',\phi\oplus(-\phi'))$ is Poincaré by [Sums of Poincaré complexes](sum-of-poincare.md) applied to $(C,\phi)$ and the [negative](poincare-neg.md) $(C',-\phi')$. $C'_r$ is a zero object outside $[0,k]\subset[0,k+1]$. The chain objects are $C'_r$ and $C_r\oplus C'_r$, which lie in $\mathcal P$. (3) The projection $\pi:\mathcal C((h,1))\to\Sigma C$, $(x,(y,y'))\mapsto y$, is a chain homotopy equivalence with inverse $\sigma:\Sigma C\to\mathcal C((h,1))$, $y\mapsto(0,(y,-hy))$. Indeed $\pi\sigma=1$, and $1-\sigma\pi=dH+Hd$ for $H(x,(y,y'))=(0,(0,(-1)^rx))$ on $\mathcal C((h,1))_r$, since $(1-\sigma\pi)(x,(y,y'))=(x,(0,hy+y'))$. (4) $\pi\psi_r=(-1)^r\phi_{r-1}h^*$, so $\pi\psi=\Sigma(\phi_\natural h^{k-*})\circ\varepsilon$ with the isomorphism $\varepsilon_r=(-1)^r:C'^{k+1-*}\to\Sigma C'^{k-*}$. Here $\phi_\natural$ is an equivalence, $h^{k-*}$ is one by [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md), and $\Sigma$ preserves equivalences by [Shifts of homotopy equivalences](../complexes/shift-equivalence.md), so $\pi\psi$ is an equivalence. Hence so is $\sigma\pi\psi$, and $\psi$ is one because it is homotopic to $\sigma\pi\psi$.

## Sources

- HS paper, Section 5 (symmetrizing a primitive)
- [Ranicki 1989, Def 3.10](../../../../../sources/paper/ranicki-1989.md) [U]

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Structure complex](../complexes/structure-complex.md)
- [The involution T](../complexes/structure-involution.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)

## Proof depends on

- [T is an involution](../complexes/structure-involution-square.md)
- [Pushforward commutes with T](../complexes/structure-push-involution.md)
- [Sums of Poincaré complexes](sum-of-poincare.md)
- [Negative of a Poincaré complex](poincare-neg.md)
- [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md)
- [Shifts of homotopy equivalences](../complexes/shift-equivalence.md)
- [Pushforward preserves composition](../complexes/functors/push-comp.md)
- [Pushforward preserves identities](../complexes/functors/push-id.md)
- [Mapping cone](../complexes/cone.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Dual complex](../complexes/dual-complex.md)
- [Dual of a chain map](../complexes/functors/dual-map.md)
- [The shift of a complex](../complexes/shift.md)
- [Pair map](pair-map.md)

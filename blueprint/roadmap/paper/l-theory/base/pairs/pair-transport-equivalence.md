---
article_id: af_28c39397fdc8578e8fe5847a
declaration: lemma
origin: bridged
---

# Transport of pairs along homotopy equivalences

Let $(f:C\to D,\delta\phi,\phi)$ be a strict $n$-dimensional Poincaré pair in $\mathrm{Kar}\,\mathcal A$. Let $h:C'\to C$ be a chain homotopy equivalence, where $C'_r$ is a zero object for every $r$ outside $[0,n-1]$. Let $\phi'\in M(C')_{n-1}$ satisfy $\partial\phi'=0$ and $T\phi'=\phi'$, and let $\chi\in M(C)_n$ satisfy $\partial\chi=h_\%\phi'-\phi$. Put $\chi'=(\chi+T\chi)/2$. Then $(fh:C'\to D,\ \delta\phi+f_\%\chi',\ \phi')$ is a strict $n$-dimensional Poincaré pair. In particular its boundary $(C',\phi')$ is Poincaré.

*Proof sketch.*
1. Symmetrize. $T\chi'=\chi'$, and $\partial\chi'=\partial\chi$ because $h_\%\phi'-\phi$ is $T$-invariant ($T\partial=\partial T$, $T^2=1$, $h_\%T=Th_\%$).
2. Boundary. By [Homologous cycles give homotopic maps](../complexes/cycle-chain-map-homotopy.md), $h\,\phi'_\natural\,h^{n-1-*}=(h_\%\phi')_\natural\simeq\phi_\natural$, an equivalence. $h$ and $h^{n-1-*}$ are equivalences ([Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md)), so $\phi'_\natural$ is one by two-out-of-three.
3. Interior. $T(\delta\phi+f_\%\chi')=\delta\phi+f_\%\chi'$, and $\partial(\delta\phi+f_\%\chi')=f_\%\phi+f_\%(h_\%\phi'-\phi)=(fh)_\%\phi'$.
4. Pair map. $\kappa:\mathcal C(fh)\to\mathcal C(f)$, $(x,y)\mapsto(x,hy)$, is a [triangular](../complexes/triangular-map.md) chain map with diagonal components $1_D$ and $\Sigma h$, hence an equivalence by [Triangular equivalences](../complexes/triangular-equivalence.md). Let $\psi'$ and $\psi$ be the pair maps of the new and the old pair. Since pair maps are linear in their data and $h_\%\phi'=\phi+\partial\chi'$, $\kappa\psi'-\psi$ is the pair map of $(f_\%\chi',\partial\chi')$, namely $r\mapsto(f\chi'_rf^*,\ (-1)^r(\partial\chi')_{r-1}f^*)$. This equals $dK+Kd$ for $K_r=(0,(-1)^r\chi'_rf^*):D^*_{n-r}\to D_{r+1}\oplus C_r$. So $\kappa\psi'\simeq\psi$ is an equivalence, and $\psi'$ is one by two-out-of-three.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the explicit null-homotopy $K$

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Pushforward of structures](../complexes/structure-push.md)

## Proof depends on

- [T is an involution](../complexes/structure-involution-square.md)
- [Pushforward commutes with T](../complexes/structure-push-involution.md)
- [Homologous cycles give homotopic maps](../complexes/cycle-chain-map-homotopy.md)
- [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md)
- [Triangular map](../complexes/triangular-map.md)
- [Triangular equivalences](../complexes/triangular-equivalence.md)

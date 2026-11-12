---
article_id: af_413bed12f4f459aae55d7d00
declaration: lemma
origin: cited
statement: formalized
lean: HSP.symLine_poincare
proof: formalized
---

# The line is Poincaré

$\lambda_\natural:\Lambda^{1-*}\to\Lambda$ is a chain homotopy equivalence in $C_\mathbb Z(\mathbb Q)$. Hence $(\Lambda,\lambda)$ is a strict $1$-dimensional symmetric Poincaré complex.

*Proof sketch.*
1. Cellular duality. Let $c\in M(\Lambda)_1$ have components $c_1(v_n^*)=e_{n+1/2}$ and $c_0(e^*_{n+1/2})=v_{n+1}$. Then $(\partial c)_0=dc_1+c_0d^*$ sends $v_n^*$ to $(v_{n+1}-v_n)+(v_n-v_{n+1})=0$, so $c$ is a cycle. Both components are isomorphisms with inverses of propagation $1$, so $c_\natural$ is an isomorphism of complexes.
2. Transpose. $Tc$ has components $(Tc)_1=c_0^*:v_n^*\mapsto e_{n-1/2}$ and $(Tc)_0=c_1^*:e^*_{n+1/2}\mapsto v_n$. Hence $\lambda=\tfrac12(c+Tc)$.
3. Homotopy. Let $h\in M(\Lambda)_2$ have the single component $h_1:\Lambda_1^*\to\Lambda_1$, $e^*_{n+1/2}\mapsto e_{n+1/2}$, of propagation $0$. Then $(\partial h)_0=dh_1$ sends $e^*_{n+1/2}$ to $v_{n+1}-v_n=(c-Tc)_0(e^*_{n+1/2})$, and $(\partial h)_1=-h_1d^*$ sends $v_n^*$ to $-e_{n-1/2}+e_{n+1/2}=(c-Tc)_1(v_n^*)$. So $c-Tc=\partial h$ and $\lambda=c-\tfrac12\partial h$.
4. By [Homologous cycles give homotopic maps](../../base/complexes/cycle-chain-map-homotopy.md), $\lambda_\natural\simeq c_\natural$, which is an isomorphism. So $\lambda_\natural$ is a homotopy equivalence.

## Sources

- [Ranicki 1980 I, §1, homotopy symmetry of cellular duality](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the explicit cycle $c$ and homotopy $h$ in this paper's conventions.

## Depends on

- [The symmetric line](symmetric-line.md)
- [Structure of the symmetric line](symmetric-line-structure.md)
- [The symmetric line is a symmetric complex](symmetric-line-cycle.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Duality map of a cycle](../../base/complexes/cycle-chain-map.md)

## Proof depends on

- [The symmetric line](symmetric-line.md)
- [Homologous cycles give homotopic maps](../../base/complexes/cycle-chain-map-homotopy.md)
- [Duality map of a cycle](../../base/complexes/cycle-chain-map.md)
- [Entries of composites of constant families](bookkeeping/constant-family-comp.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)

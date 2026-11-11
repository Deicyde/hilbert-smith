---
article_id: af_8f0e26277348e8d407b0374c
declaration: def
origin: cited
statement: formalized
lean: HSP.ultL
---

# Ultimate L-group

$\mathbb L_k(\mathcal A)$ is the colimit of the sequence of groups
$$L^{\langle 0\rangle}_k(\mathcal A)\xrightarrow{t}L^{\langle -1\rangle}_k(\mathcal A)\xrightarrow{t}L^{\langle -2\rangle}_k(\mathcal A)\xrightarrow{t}\cdots,$$
where $t$ is the transition map. Write $\iota_j:L^{\langle -j\rangle}_k(\mathcal A)\to\mathbb L_k(\mathcal A)$ for the map from stage $j$, and $\mathrm{cls}:=\iota_0:L^p_k(\mathcal A)\to\mathbb L_k(\mathcal A)$. *Notation.* For a strict symmetric Poincaré complex $(C,\phi)$ in $\mathcal A$ itself, $\mathrm{cls}(C,\phi)$ abbreviates $\mathrm{cls}[\mathrm{emb}_{\mathcal A}C,\phi]=\mathrm{cls}[(C,1),\phi]$, the class of its [image](../../base/pairs/functor-poincare.md) under the strict duality functor $\mathrm{emb}_{\mathcal A}:\mathcal A\to\mathrm{Kar}\,\mathcal A$, the [Karoubi embedding](../../base/categories/karoubi-embedding.md): chain objects $(C_r,1)$, with the same differentials and structure maps.

## Sources

- [Carlsson-Pedersen 1995, Def 4.16](../../../../../sources/paper/carlsson-pedersen-1995.md); [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- HS paper, Section 1 (there the ultimate group is a homotopy group of a spectrum; this paper uses the group-level colimit as its definition)

## Depends on

- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Transition map](../../localization/transitions/transition-map.md)
- [Embedding into the idempotent completion](../../base/categories/karoubi-embedding.md)
- [Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)

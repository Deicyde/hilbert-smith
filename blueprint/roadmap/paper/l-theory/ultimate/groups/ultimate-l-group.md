---
article_id: af_8f0e26277348e8d407b0374c
declaration: def
origin: cited
statement: formalized
lean: HSP.ultL
---

# Ultimate L-group

$\mathbb L_k(\mathcal A)$ is the colimit of the [sequence of lower L-groups](lower-l-sequence.md)
$$L^{\langle 0\rangle}_k(\mathcal A)\xrightarrow{t}L^{\langle -1\rangle}_k(\mathcal A)\xrightarrow{t}L^{\langle -2\rangle}_k(\mathcal A)\xrightarrow{t}\cdots,$$
where $t$ is the transition map. The maps $\iota_j:L^{\langle -j\rangle}_k(\mathcal A)\to\mathbb L_k(\mathcal A)$ from the stages and the class map $\mathrm{cls}=\iota_0:L^p_k(\mathcal A)\to\mathbb L_k(\mathcal A)$ are defined in their own articles, the stage maps and the class map.

## Sources

- [Carlsson-Pedersen 1995, Def 4.16](../../../../../sources/paper/carlsson-pedersen-1995.md); [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- HS paper, Section 1 (there the ultimate group is a homotopy group of a spectrum; this paper uses the group-level colimit as its definition)

## Depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [Sequence of lower L-groups](lower-l-sequence.md)

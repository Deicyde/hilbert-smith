---
article_id: af_736bd70c653658fbcd13facb
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.meshSequence
---
# Mesh sequence

Fix a local datum, and let $k_0$ be the [mesh start](../mesh/mesh-start.md): the least integer $k_0\ge8$ with $3\omega(2h_0)+8h_0\le1/16$, where $h_0=4/k_0$ and $\omega$ is the [modulus of the track family](../approximations/modulus.md). Set $k_i=k_0+i$ and $h_i=4/k_i$. The inequality then holds for every $h_i$ because $\omega$ is nondecreasing. In particular $h_i\le1/128$.

## Sources
- New: no argument compares two levels.
## Depends on
- [Mesh start](../mesh/mesh-start.md)
- [Modulus of the track family](../approximations/modulus.md)
## Proof depends on
- [Properties of completed maps](../approximations/completed-maps-properties.md)

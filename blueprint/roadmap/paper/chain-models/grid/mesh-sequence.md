---
article_id: af_736bd70c653658fbcd13facb
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.meshSequence, HSP.ChainModels.meshSequence_spec, HSP.ChainModels.meshSequence_mesh_le
---
# Mesh sequence

Fix a local datum, and let $k_0$ be the [mesh start](../mesh/mesh-start.md): the least integer $k_0\ge8$ with $3\omega(2h_0)+8h_0\le1/16$, where $h_0=4/k_0$ and $\omega$ is the [modulus of the track family](../approximations/modulus.md). Set $k_i=k_0+i$ and $h_i=4/k_i$. The inequality then holds for every $h_i$ because $\omega$ is nondecreasing. In particular $h_i\le1/128$.

## Sources
- New: no argument compares two levels.
## Depends on

- [Modulus of the track family](../approximations/modulus.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [Properties of completed maps](../approximations/completed-maps-properties.md)
- [Completed map](../approximations/completed-map.md)
- [The completed map on Euclidean space](../approximations/maps/completed-map-euclid.md)
- [Track defect](../approximations/maps/track-defect.md)
- [The track family](../approximations/maps/track-family.md)
- [The track map on Euclidean space](../approximations/maps/track-map-euclid.md)
- [Torus test map](../approximations/torus-test-map.md)
- [The torus](torus.md)
- [Mesh start](../mesh/mesh-start.md)
- [The quotient Euclidean metric](../torus/dist2.md)
- [The lift](../torus/lift.md)
- [The round sphere](../../corner/round-sphere.md)
- [Representatives of the finite quotients](../../local-data/control/representative-map.md)

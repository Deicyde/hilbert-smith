---
article_id: af_48c794d7fca845cbde32fdcf
declaration: structure
origin: bridged
statement: formalized
lean: HSP.FixedLocalData
---

# Fixed local data

Fixed local data in dimension $n$, with constants $(D,\rho_+)$, consist of:
1. a local datum with constants $(D,\rho_+)$ in dimension $n$;
2. a pinch radius $\rho$ with $0<\rho<\rho_+$;
3. buffer radii $0<r<R<t<u$.

From these one reads off the test map $f$ of radius $\rho$ and the control space $(T,d_T)$ with its $C_p$-action. None of these depends on a level $i$: the levels $i\ge1$, with $G_i$, $P_i$, $\chi_i$ and $r_i$, are chosen afterwards. The exterior $Z_0$ about $0$, the space $Z=T\times Z_0$ and the cut sets are not part of the fixed local data: the corner chapter's standing data define them from $T$ and the radius $R$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (buffer radii, display (8.8))
- New: the buffer radii are Euclidean radii about $0$

## Depends on

- [Local datum](../chart/local-datum.md)

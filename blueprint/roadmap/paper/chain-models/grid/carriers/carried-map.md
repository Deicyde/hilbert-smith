---
article_id: af_aed0e0bcda41fc1612f83f4b
declaration: def
origin: cited
statement: formalized
lean: HSP.ChainModels.Carrier.IsCarried
---
# Carried maps

Let $\Gamma$ be a [carrier](acyclic-carriers.md) from a finite based chain complex $E$, with basis elements $e$ of each $E_r$, to a rational chain complex $F$ with augmentation $\varepsilon$. Let $\sigma:\mathbb Z\to\mathbb Z$, and let $u$ be a family of linear maps $u_r:E_r\to F_{\sigma(r)}$; for instance $u$ is a linear map of degree $m$ when $\sigma(r)=r+m$, a chain map when $\sigma=\mathrm{id}$, and a homotopy when $\sigma(r)=r+1$. Then $u$ is *carried by* $\Gamma$ if $u_r(e)\in\Gamma(e)_{\sigma(r)}$ for every $r$ and every basis element $e$ of $E_r$.

## Sources
- [Munkres 1984, acyclic carriers](../../../../../sources/paper/munkres-1984.md) [U]; HS paper, Section 7.

## Depends on
- [Carriers](acyclic-carriers.md)

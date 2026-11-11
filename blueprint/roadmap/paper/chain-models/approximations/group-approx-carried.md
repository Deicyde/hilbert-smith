---
article_id: af_d019634c542cb492d6dd2ba1
declaration: lemma
origin: bridged
---
# Carried group approximations

For every $g\in G_i$, $a_g=a^T_g\otimes1_P$ where $a^T_g$ is a chain map of $C(k_i)$ carried by $\Gamma_{\widehat{r_i(g)}}$ of [chain approximations exist](chain-approx-exists.md), with $a^T_g|_{E(k_i)}=1$ and $\varepsilon a^T_g=\varepsilon$.

*Proof sketch.* For $g\ne0$ this is the choice made in [chain approximation](chain-approx.md). For $g=0$, $r_i(0)=0$, so $\widehat{r_i(0)}=\mathrm{id}$, and the identity is carried by $\Gamma_{\mathrm{id}}(c)=\mathrm{Box}_{k_i}(N_{h_i}(|c|))$, which contains $c$ by [box hull properties](../grid/box-hull-properties.md) (3).

## Sources
- New.
## Depends on
- [Group approximations](group-approx.md), [chain approximations exist](chain-approx-exists.md)
## Proof depends on
- [Chain approximation](chain-approx.md), [completed map](completed-map.md), [box hull properties](../grid/box-hull-properties.md), [representatives](../../local-data/control/representative-map.md)

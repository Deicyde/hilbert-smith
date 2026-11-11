---
article_id: af_cd210e55681d31be0a2016d7
declaration: def
origin: background
statement: formalized
lean: HSP.StructureCx.push
---

# Pushforward of structures

A chain map $g:C\to D$ gives a chain map $g_\%:M(C)\to M(D)$, $(g_\%f)_r=g_r f_r g_{n-r}^*$; in pair indices, $(g_\%f)_{r,s}=g_rf_{r,s}g_s^*$. Pushforward is functorial: $(hg)_\%=h_\%g_\%$ and $1_\%=1$.

## Sources

- HS paper, Section 5

## Depends on

- [Structure complex](structure-complex.md)

---
article_id: af_c823b5a9414edb452988571e
declaration: abbrev
origin: background
statement: formalized
lean: HSP.StructureCx
---

# Structure complex

For a complex $C$, $M(C)_n=\prod_{r+s=n}\mathrm{Hom}(C_s^*,C_r)$, the product over the pairs $(r,s)\in\mathbb Z^2$ with $r+s=n$, which is a finite product when $C$ is bounded. Write $f_{r,s}$ for the component of $f$ at $(r,s)$, and $f_r=f_{r,n-r}$. The differential $\partial:M(C)_n\to M(C)_{n-1}$ is $(\partial f)_{r,s}=d f_{r+1,s}+(-1)^r f_{r,s+1} d^*$, that is $(\partial f)_r=d f_{r+1}+(-1)^r f_r d^*$. Then $\partial^2=0$, so $M(C)$ is a complex of $\mathbb Q$-vector spaces.

## Sources

- HS paper, Section 5

## Depends on

- [Small Q-linear category with strict duality](../categories/duality-category.md)

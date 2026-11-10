---
article_id: af_4c6e8ae3f3f684ae270ac7e9
declaration: lemma
origin: bridged
---

# Averages of witnesses

With $I,\kappa,\mu$ as in [Average propagation](average-propagation.md), let each $e_k$ be an exterior witness of type $\chi_i(\kappa k)$ with bound $\delta$ through $W_k$. Then $\sum_k\mu_k\operatorname{Ind}_{\kappa k}e_k=xy$ through $\bigoplus_k\operatorname{Ind}W_k$, which is labeled within $\delta$ of $Z$, with $x,y$ equivariant of propagation at most $\delta$.

*Proof sketch.*
1. With $e_k=x_ky_k$, $\operatorname{Ind}_{\kappa k}e_k=\operatorname{Ind}_{\kappa k}x_k\,\operatorname{Ind}_0y_k$ ([Sheet shifts multiply](sheet-shift-mul.md)).
2. Both factors are equivariant of propagation at most $\delta$ ([Sheet translation](sheet-translation.md)); labels of $\operatorname{Ind}W_k$ stay within $\delta$ of $Z$ because $Z$ is invariant.
3. Stack as in [Sums of witnesses](witness-sum.md); the stacked factors are equivariant.

## Sources

- HS paper, Sections 10 and 11.

## Depends on

- [Exterior witnesses](exterior-witness.md)
- [Sheet shift](sheet-shift.md)

## Proof depends on

- [Sheet shifts multiply](sheet-shift-mul.md)
- [Sheet translation](sheet-translation.md)
- [Sums of witnesses](witness-sum.md)

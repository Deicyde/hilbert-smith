---
article_id: af_1c549630b84dc292f6335433
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.exists_localDatum
---

# A local datum from a faithful action

Let $p$ be a prime, let $\mathbb Z_p$ act jointly continuously and faithfully on a connected $n$-manifold $M$ (a connected Hausdorff space with an atlas of charts onto open subsets of $\mathbb R^n$, with no countability assumption), and let $0<D\le1/64$. Then there are $\rho_+\in(0,1/4)$ and a local datum with constants $(D,\rho_+)$ in dimension $n$.

*Proof sketch.*
1. Take a point $x_0$ with no fixed neighbourhood.
2. Take a chart $e$ at $x_0$ and $s>0$ with $\overline B(e(x_0),4s)$ inside its target. Set $\psi=(e-e(x_0))/s$. Then $\psi(x_0)=0$, the target of $\psi$ contains $\overline B(0,4)$, and $C=\psi^{-1}(\overline B(0,3))$, taken inside the domain of $\psi$, is compact.
3. Uniformly small displacement near the identity, for $C$ and $\delta=D/2$, followed by the basis property of the $H_j$, gives $j$ such that, for all $a\in H_j$ and $m\in C$, the point $a\cdot m$ lies in the domain of $\psi$ and $|\psi(a\cdot m)-\psi(m)|\le D/2$.
4. $\psi^{-1}(B(0,1))$ is a neighbourhood of $x_0$, so it contains some $y\notin\operatorname{Fix}_j(M)$. Since $\operatorname{Fix}_j(M)$ is closed there is $\rho'>0$ such that no point of the domain of $\psi$ mapped into $\overline B(\psi(y),\rho')$ lies in $\operatorname{Fix}_j(M)$. Put $\rho_+=\min(\rho',1/8)$.
5. Recentre with $\varphi=\psi-\psi(y)$. Since $|\psi(y)|<1$, the points of the domain mapped by $\varphi$ into $\overline B(0,2)$ lie in $C$.
6. Let $\Omega_M=H_j\cdot\varphi^{-1}(B(0,2))$, an open invariant set inside the domain, and $\Omega=\varphi(\Omega_M)\supseteq B(0,2)$. For $x=\varphi(b\cdot m)$ with $b\in H_j$ and $m\in\varphi^{-1}(B(0,2))$, and any $a$, the triangle inequality through $\varphi(m)$ bounds the displacement by $D/2+D/2$.
7. Define $a\star x=\varphi((p^ja)\cdot\varphi^{-1}(x))$ on $\Omega$. This is a jointly continuous action, because $a\mapsto p^ja$ is additive.
8. If $|x|\le\rho_+$, then $\varphi^{-1}(x)\notin\operatorname{Fix}_j(M)$, so some $p^ja$ moves it, and $a\star x\ne x$.

This result rests, through the good point, on the open statement [Newman's theorem on fixing an open set](../../inputs/newman/newman-open-set.md).

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the chart and the small subgroup)
- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 51-60
- New: recentring at a point of the unit ball outside $\operatorname{Fix}_j(M)$, with radii $4,3,2,1$, the bound $D/2$ and $\rho_+=\min(\rho',1/8)$

## Depends on

- [Local datum](local-datum.md)

## Proof depends on

- [A point with no fixed neighbourhood](../subgroups/good-point.md)
- [Uniformly small displacement near the identity](../subgroups/small-displacement.md)
- [The subgroups $H_j$ form a basis at $0$](../subgroups/padic-subgroups-basis.md)
- [Fixed sets are closed](../subgroups/fixed-sets-closed.md)
- [The subgroups $H_j$](../subgroups/padic-subgroups.md)
- [Fixed sets of the subgroups $H_j$](../subgroups/fixed-sets.md)

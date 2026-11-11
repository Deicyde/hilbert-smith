---
article_id: af_d01b3ab7c021aae7f64b3646
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.SymPair.transport
---

# Transport of pairs along isomorphisms

Let $(f:C\to D,\delta\phi,\phi)$ be a strict $n$-dimensional Poincaré pair in a duality category $\mathcal B$, let $u:C'\to C$ be an isomorphism of complexes, let $\phi'\in M(C')_{n-1}$ satisfy $u_\%\phi'=\phi$, and let $s\in\{1,-1\}$. Then $(fu:C'\to D,\ s\,\delta\phi,\ s\,\phi')$ is a strict $n$-dimensional Poincaré pair.

*Proof sketch.* (1) Boundary: $\phi'=(u^{-1})_\%\phi$, so $\phi'$ is a $T$-invariant cycle, $\phi'_\natural=u^{-1}\phi_\natural(u^{-1})^{n-1-*}$ is an equivalence, and $C'_r\cong C_r$ is a zero object outside $[0,n-1]$. Negating keeps all of this. (2) $T(s\delta\phi)=s\delta\phi$ and $\partial(s\delta\phi)=sf_\%\phi=(fu)_\%(s\phi')$. (3) The isomorphism $\kappa:\mathcal C(fu)\to\mathcal C(f)$, $(x,y)\mapsto(x,uy)$, carries the pair map $\psi'$ of the new data to $s\psi$: its second component is $s(-1)^ru\phi'_{r-1}u^*f^*=s(-1)^r\phi_{r-1}f^*$. So $\psi'=\kappa^{-1}(s\psi)$ is an equivalence.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign parameter merges negation and transport into one statement

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Pushforward of structures](../complexes/structure-push.md)

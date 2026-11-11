---
article_id: af_89d47ae86c5c708d99168b77
declaration: theorem
origin: bridged
---

# Split pair criterion

Let $f:C\to D$ be a chain map of complexes in a duality category $\mathcal B$, $\phi\in M(C)_{n-1}$ with $\partial\phi=0$, and $\delta\phi\in M(D)_n$ with $T\delta\phi=\delta\phi$ and $\partial\delta\phi=f_\%\phi$. Suppose $f$ is degreewise split injective, with a chosen splitting: maps $s_r:D_r\to C_r$, $i_r:Q_r\to D_r$, $\pi_r:D_r\to Q_r$ with $s f=1$, $\pi i=1$, $\pi f=0$, $s i=0$ and $f s+i\pi=1$. Let $D/C$ be the complex with terms $Q_r$ and differential $\pi d i$; then $\pi:D\to D/C$ is a chain map. The maps $\theta_r=\delta\phi_r\pi^*_{n-r}:Q^*_{n-r}\to D_r$ form a chain map $\theta:(D/C)^{n-*}\to D$, and the [pair map](pair-map.md) $\psi:D^{n-*}\to\mathcal C(f)$ is a chain homotopy equivalence iff $\theta$ is.

*Proof sketch.*
1. $D/C$ and $\pi$. $\pi d=\pi d(fs+i\pi)=\pi fds+(\pi di)\pi=(\pi di)\pi$, using $df=fd$ and $\pi f=0$. Hence $\pi$ commutes with the differentials, and $(\pi di)^2=\pi d(1-fs)di=-\pi fdsdi=0$.
2. $\theta$ is a chain map. The defect of $\theta$ is $(\partial\delta\phi)\pi^*$, which is $(f\phi f^*)\pi^*=f\phi(\pi f)^*=0$ in each degree.
3. The projection $p:\mathcal C(f)\to D/C$, $(x,y)\mapsto\pi x$, is a chain homotopy equivalence. It is a chain map because $\pi f=0$. The isomorphism $(x,y)\mapsto((sx,y),\pi x)$ identifies $\mathcal C(f)$ with a [twisted sum](../complexes/twisted-sum.md) $\mathcal C(1_C)\oplus_\tau(D/C)$, $\tau(q)=(sdiq,0)$, and carries $p$ to the [triangular](../complexes/triangular-map.md) projection onto $0\oplus(D/C)$, whose diagonal components are $\mathcal C(1_C)\to0$ and $1$. $\mathcal C(1_C)$ is contractible via $(x,y)\mapsto(0,(-1)^rx)$, so $p$ is an equivalence by [Triangular equivalences](../complexes/triangular-equivalence.md).
4. $p\psi=g$ with $g_r=\pi\delta\phi_r:D^*_{n-r}\to Q_r$, the first component of the pair map followed by $\pi$. By step 3 and two-out-of-three, $\psi$ is an equivalence iff $g$ is.
5. Duality. The dual $g^{n-*}:(D/C)^{n-*}\to(D^{n-*})^{n-*}$ has components $\delta\phi_{n-r}^*\pi^*$. The double dual $(D^{n-*})^{n-*}$ has terms $D_r$ and differential $(-1)^{n+1}d$, and $\nu_r=(-1)^{r(n+1)}$ is an isomorphism of complexes from it to $D$. $T\delta\phi=\delta\phi$ gives $\delta\phi_{n-r}^*=(-1)^{r(n-r)}\delta\phi_r$, and $r(n+1)+r(n-r)\equiv r(1-r)\equiv0\pmod 2$, so $\nu\,g^{n-*}=\theta$.
6. By [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md), $g$ is an equivalence iff $g^{n-*}$ is: one direction is that lemma, and the other applies it to $g^{n-*}$ and uses the same double-dual isomorphisms on both sides. So $g$ is an equivalence iff $\theta$ is.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U] (the relative duality map of a pair)
- New: the explicit identification in the paper's sign conventions

## Depends on

- [Pair map](pair-map.md)
- [Mapping cone](../complexes/cone.md)
- [Dual complex](../complexes/dual-complex.md)
- [Structure complex](../complexes/structure-complex.md)
- [The involution T](../complexes/structure-involution.md)
- [Pushforward of structures](../complexes/structure-push.md)

## Proof depends on

- [Twisted sum](../complexes/twisted-sum.md)
- [Triangular map](../complexes/triangular-map.md)
- [Triangular equivalences](../complexes/triangular-equivalence.md)
- [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md)

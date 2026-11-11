---
article_id: af_b03e52cc71118feb8b335c8c
declaration: theorem
origin: bridged
---

# Abstract nilpotence

Let $F$ be a Mayer-Vietoris functor on a lattice $\Lambda$ with a natural endomorphism $\nu$. Let $s\ge1$ and $T_1,\dots,T_s\in\Lambda$. Suppose that, for each $a$ and every $S\le T_a$, $\nu_S=0$ on $F_k(S)$ for all $k$. Then $\nu^s=0$ on $F_k(T_1\vee\dots\vee T_s)$ for all $k$.

*Proof sketch.* Induction on $s$, for all families at once.
1. For $s=1$, the hypothesis with $S=T_1$ gives the claim.
2. For $s>1$, put $A=T_1\vee\dots\vee T_{s-1}$, $B=T_s$ and $Y=A\wedge B\le T_s$.
3. For $x\in F_k(A\vee B)$, naturality gives $\partial_{A,B}(\nu x)=\nu\,\partial_{A,B}x$. This is $0$ because $\nu_Y=0$ on $F_{k-1}(Y)$.
4. Middle exactness writes $\nu x=i(a)+i(b)$.
5. Then $\nu^{s-1}a=0$ by induction applied to $T_1,\dots,T_{s-1}$, and $\nu b=0$ by hypothesis. Naturality of $i$ gives $\nu^s x=i(\nu^{s-1}a)+i(\nu^{s-2}\nu b)=0$, where $s-2\ge0$.

## Sources

- HS paper, Section 4 (Nilpotence).
- New: the induction stays inside one lattice, so no relabeling to a smaller space is needed.

## Depends on

- [Mayer-Vietoris functor](mayer-vietoris-functor.md)
- [Natural endomorphism](natural-endomorphism.md)

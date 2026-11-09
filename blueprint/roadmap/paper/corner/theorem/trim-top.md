---
article_id: af_d2c0bd3ca136a495d0412ba4
declaration: lemma
origin: bridged
---

# Trimming the top

Let $\mathcal P$ be idempotent complete and additive. Let $D'$ be a $\mathbb Z$-graded complex and $C$ a complex with $C_k=0$ for $k>N$, with chain maps $\iota:D'\to C$, $r:C\to D'$ and $r\iota\simeq1$. Then there are a complex $D''$ with $D''_k=0$ for $k>N$ and $D''_k=D'_k$ for $k<N$, and chain maps $j:D''\to D'$, $\pi:D'\to D''$ with $\pi j=1$ and $j\pi\simeq1$.

*Proof sketch.*
1. Let $r\iota-1=dh+hd$. For $k>N$, $\iota_k=0$, so $-1=d_{k+1}h_k+h_{k-1}d_k$.
2. $p=-d_{N+1}h_N$ is idempotent on $D'_N$ (degree $N+1$ relation and $d^2=0$). Also $d_Np=0$ and $pd_{N+1}=d_{N+1}$.
3. Put $D''_N=\operatorname{im}(1-p)$ (split in $\mathcal P$), zero above $N$, $D'$ below; $j,\pi$ are the inclusion and $1-p$ in degree $N$, the identity below.
4. $j\pi-1=dk+kd$ with $k_m=h_m$ for $m\ge N$ and $k_m=0$ for $m<N$.

## Sources

- New: elementary; no top degree of $D'$ is needed.

## Depends on

- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)

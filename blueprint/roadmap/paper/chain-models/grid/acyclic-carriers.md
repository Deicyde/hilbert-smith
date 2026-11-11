---
article_id: af_684eec75c9fea73a99ec6404
declaration: structure
origin: cited
statement: formalized
lean: HSP.ChainModels.Carrier
---
# Carriers

Let $E$ be a finite based chain complex in degrees $\ge0$, and $F$ a rational chain complex with augmentation $\varepsilon:F_0\to\mathbb Q$, so $\varepsilon d_1=0$. A subcomplex $\Gamma\subseteq F$ is *augmented acyclic* if $H_r(\Gamma)=0$ for $r>0$ and $\varepsilon$ induces an isomorphism $H_0(\Gamma)\cong\mathbb Q$. A *carrier* $\Gamma$ assigns to each basis element $e$ of $E$ an augmented acyclic subcomplex $\Gamma(e)\subseteq F$, with $\Gamma(e')\subseteq\Gamma(e)$ whenever $e'$ occurs in $de$ (has a nonzero coefficient there). A linear map $u$ from $E$ to $F$ sending each $E_r$ into some $F_{\sigma(r)}$, for instance of degree $m$ with $\sigma(r)=r+m$, is *carried* if $u(e)\in\Gamma(e)$ for every $e$.

## Sources
- [Munkres 1984, acyclic carriers](../../../../sources/paper/munkres-1984.md) [U]; HS paper, Section 7.

## Depends on

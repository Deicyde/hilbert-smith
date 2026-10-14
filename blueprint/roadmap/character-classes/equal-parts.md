---
article_id: af_d7367ec268e753ebcf15e008
declaration: theorem
origin: cited
---

# Equal parts

Fix $k \geq 1$, $m = p^k$, the cyclic partition
$D_i = \zeta^iD_0$ of $\Lambda$, and the sheet region $V$ with
multiplier $\beta$ from finite quotient sheets. If
$h : Y \to S^d$ is constant on $Y \setminus V$, then
$z_0(h) = \cdots = z_{m-1}(h)$ in $E_d(S^d)$.

*Proof sketch.* Multiplication by the locally constant unit
$\beta$ is a real isometry of the restricted coefficient sheaf;
with the paper's $T$ convention it shifts
$\lambda$-eigensheaves to $\zeta^{-1}\lambda$-eigensheaves,
cyclically permuting the partition. After the proper restricted
pushforward it conjugates $e_i$ to $e_{i-1}$ modulo $m$; the
germ theorem promotes the isometry to the quotient, where the
twisted (and untwisted) forms become isometric, and integral
localization transfers the equality.

## Sources

- [Preprint source map: `prop:equal-parts`](../../sources/preprint.md)

## Depends on

- [Character classes](character-classes.md)

## Proof depends on

- [Finite quotient sheets](../local-tests/finite-sheets.md)
- [Germ description](../localization/germs.md)
- [Contractible quotient](../sphere-lattice/contractible-quotient.md)

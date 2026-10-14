---
article_id: af_4a651f56b0520f1bf8c8e6cb
declaration: theorem
origin: cited
---

# Moving a test

For every nonempty open $V \subset Y \setminus \{y_\infty\}$, with
$F = Y \setminus V$, there are a positive integer $s$, a degree-$s$
map $D_s : S^d \to S^d$, and a map $h : Y \to S^d$ with
$h \simeq D_s a$ and $h|_F \equiv b$ for some $b \in S^d$. In
particular $h(y_\infty) = b$ and the nonconstant source lies over
$V$. The degree $s$ may depend on $V$ (and hence on $k$ for sheet
regions).

*Proof sketch.* The degree-one pinch can be transported along a
path in $W$ to a ball over $V$, so $aq$ is homotopic to a map
constant on $q^{-1}(F)$; the restricted orbit map meets the orbit
pullback hypotheses, giving $(a|_F)^*\gamma_d = 0$. Odd-sphere
nullhomotopy kills some $D_s a|_F$, and homotopy extension promotes
the nullhomotopy to $Y$.

## Sources

- [Preprint source map: `prop:move-test`](../../sources/preprint.md)

## Depends on

- [Averaged degree-one test](averaged-test.md)
- [Finite quotient sheets](finite-sheets.md)

## Proof depends on

- [Averaged degree-one test](averaged-test.md)
- [Rational orbit pullback](orbit-injectivity.md)
- [Odd-sphere nullhomotopy](odd-sphere-null.md)
- [Homotopy extension](neighborhood-extension.md)
- [Finite quotient sheets](finite-sheets.md)

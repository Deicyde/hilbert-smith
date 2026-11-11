---
article_id: af_aadc3dc0de7f1726e57fed77
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.vadd_mem_thickening_iff
---

# Translates and thickenings of an invariant set

Let the $C_p$-action on $X$ be isometric and $S\subset X$ invariant. For $c\in C_p$, a real $\varepsilon$ and $y\in X$, $c+y$ lies in the open $\varepsilon$-thickening of $S$ if and only if $y$ does.

*Proof sketch.* If $d(y,z)<\varepsilon$ with $z\in S$, then $c+z\in S$ and $d(c+y,c+z)=d(y,z)<\varepsilon$. Apply this to $-c$ for the converse.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

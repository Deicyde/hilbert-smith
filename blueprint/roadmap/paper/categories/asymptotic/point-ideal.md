---
article_id: af_298e54a8953f359d7eb4a903
declaration: lemma
origin: bridged
---

# Point ideal

A morphism $(u_i):M\to M'$ of the [sequence category](point-sequence-category.md) factors through an object of the [finite-support subcategory](eventually-zero-subcategory.md) $\mathcal S_{\mathbf G}$ if and only if $u_i=0$ for all but finitely many $i$.

*Proof sketch.* (⇒) If $(u_i)=(w_i)(v_i)$ through an object $V$ that is the zero object in every coordinate $i\ge N$, then $u_i$ factors through the zero object for $i\ge N$. (⇐) If $u_i=0$ for $i\ge N$, then $(u_i)$ factors through $M_{<N}$, which has $n_i$ in the coordinates $i<N$ and the zero object elsewhere, by the coordinate projection followed by $(u_i)$ restricted to it.

## Sources

- HS paper, Section 3

## Depends on

- [Finite-support subcategory](eventually-zero-subcategory.md)

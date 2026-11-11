---
article_id: af_298e54a8953f359d7eb4a903
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.SCat.ideal_iff
---

# Point ideal

A morphism $(u_i):M\to M'$ of the [sequence category](point-sequence-category.md) factors through an object of the [finite-support subcategory](eventually-zero-subcategory.md) $\mathcal S_{\mathbf G}$ if and only if $u_i=0$ for all but finitely many $i$.

*Proof sketch.* (⇒) If $(u_i)=(w_i)(v_i)$ through an object $V$ of $\mathcal S_{\mathbf G}$, then for every $i$ outside the finite set where $V$ is nonzero, $u_i$ factors through the zero object, so $u_i=0$. (⇐) If $u_i=0$ outside a finite set $F$, then $(u_i)$ factors through the object that has $n_i$ in the coordinates $i\in F$ and the zero object elsewhere: by identity matrices followed by $(u_i)$ on $F$, and by zero elsewhere.

## Sources

- HS paper, Section 3

## Depends on

- [Finite-support subcategory](eventually-zero-subcategory.md)

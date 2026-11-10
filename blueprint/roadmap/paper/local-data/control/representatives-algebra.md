---
article_id: af_0dc07d9371529837a1ebbec1
declaration: lemma
origin: bridged
---

# Algebra of the representatives

Let $i\ge1$, let $q_i:\mathbb Z_p\to G_i=\mathbb Z/p^i\mathbb Z$ be reduction modulo $p^i$ and $\chi_i:G_i\to C_p$ reduction modulo $p$. For all $g,g'\in G_i$:
1. $q_i(r_i(g))=g$ and $r_i(0)=0$;
2. $r_i(g)+r_i(g')-r_i(g+g')\in H_i$;
3. $\chi_i(g)=q_1(r_i(g))$.

*Proof sketch.* (1) and (3) are read off from the definition. For (2), the element reduces to $g+g'-(g+g')=0$ modulo $p^i$, so it lies in the kernel of $q_i$, which is $H_i$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the finite quotients, display (8.9))

## Depends on

- [Representatives of the finite quotients](representative-map.md)
- [The subgroups $H_j$](../subgroups/padic-subgroups.md)

## Proof depends on

- [The kernel of reduction modulo $p^i$](reduction-kernel.md)

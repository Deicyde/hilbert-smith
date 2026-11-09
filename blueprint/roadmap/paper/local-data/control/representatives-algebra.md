---
article_id: af_0dc07d9371529837a1ebbec1
declaration: lemma
origin: bridged
---

# Algebra of the representatives

Let $\ell\ge1$, let $q_\ell:\mathbb Z_p\to G_\ell=\mathbb Z/p^\ell\mathbb Z$ be reduction modulo $p^\ell$ and $\chi_\ell:G_\ell\to C_p$ reduction modulo $p$. For all $g,g'\in G_\ell$:
1. $q_\ell(r_\ell(g))=g$ and $r_\ell(0)=0$;
2. $r_\ell(g)+r_\ell(g')-r_\ell(g+g')\in H_\ell$;
3. $\chi_\ell(g)=q_1(r_\ell(g))$.

*Proof sketch.* (1) and (3) are read off from the definition. For (2), the element reduces to $g+g'-(g+g')=0$ modulo $p^\ell$, so it lies in the kernel of $q_\ell$, which is $H_\ell$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the finite quotients, display (8.9))

## Depends on

- [Representatives of the finite quotients](representative-map.md)
- [The subgroups $H_j$](../subgroups/padic-subgroups.md)

## Proof depends on

- [The kernel of reduction modulo $p^\ell$](reduction-kernel.md)

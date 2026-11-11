---
article_id: af_f42dcd7627348993adbdc17c
declaration: lemma
origin: background
statement: formalized
lean: HSP.FiltQuot.ideal_closed
proof: formalized
---

# Maps factoring through a dual-closed subcategory form an ideal

Let $\mathcal U\subset\mathcal A$ be a [full additive subcategory with $\mathcal U^*\subset\mathcal U$](dual-additive-subcategory.md). The [maps factoring through an object of $\mathcal U$](filtration-ideal.md) form a $\mathbb Q$-linear ideal closed under the duality:
1. $0\in I_{\mathcal U}(M,N)$;
2. if $f,g\in I_{\mathcal U}(M,N)$, then $f+g\in I_{\mathcal U}(M,N)$;
3. if $f\in I_{\mathcal U}(M,N)$, then $-f\in I_{\mathcal U}(M,N)$ and $cf\in I_{\mathcal U}(M,N)$ for every $c\in\mathbb Q$;
4. if $f\in I_{\mathcal U}(M,N)$, then $fh\in I_{\mathcal U}(L,N)$ for every $h:L\to M$ and $hf\in I_{\mathcal U}(M,P)$ for every $h:N\to P$;
5. if $f\in I_{\mathcal U}(M,N)$, then $f^*\in I_{\mathcal U}(N^*,M^*)$.

*Proof sketch.* (1) $0$ factors through a zero object lying in $\mathcal U$. (2) If $f=ba$ through $V$ and $g=dc$ through $W$, then $f+g=(b\,\mathrm{pr}_V+d\,\mathrm{pr}_W)(\mathrm{in}_V a+\mathrm{in}_W c)$ through a sum of $V$ and $W$ lying in $\mathcal U$. (3) $-f=b(-a)$ and $cf=b(ca)$. (4) $fh=b(ah)$ and $hf=(hb)a$. (5) $f^*=a^*b^*$ through $V^*\in\mathcal U$.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Additive subcategory closed under duality](dual-additive-subcategory.md)
- [Maps factoring through a subcategory](filtration-ideal.md)
- [Small Q-linear category with strict duality](duality-category.md)

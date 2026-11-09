---
declaration: lemma
origin: bridged
---

# Restriction on $L^p_4$

For $H\le G$, $x\in L^p_4(\mathrm{Free}(\mathbb Q[G]))$ and $h\in H$, $\mathrm{Sign}_H((\mathrm{res}^G_H)_*x)(h)=\mathrm{Sign}_G(x)(h)$.

*Proof sketch.* Choose a representative. Restriction does not change the matrices, so $H^2(\mathrm{res}\,C;\mathbb R)=H^2(C;\mathbb R)$ and $b_{\mathrm{res}\,C}=b_C$, with the action restricted. Apply [the form rule](form-signature-restrict.md).

## Sources

- HS paper, Section 3 (used in the divisibility step)

## Depends on

- [Restriction functor](restriction-functor.md)
- [Signature hom](signature-hom.md)
- [Induced homomorphism](../l-theory/base/induced-map.md)

## Proof depends on

- [Restriction of the form signature](form-signature-restrict.md)

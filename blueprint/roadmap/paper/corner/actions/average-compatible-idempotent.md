---
article_id: af_ed0284fcb7fca987c8468b5a
declaration: lemma
origin: bridged
---

# The average is a compatible idempotent

For a graph-type homotopy action, the [average](average.md) $(E,\mathcal H,\mathcal V)$ consists of morphisms of $\mathcal B_{\mathbf G,Z}(T\times S^n)$ and is a [compatible homotopy idempotent](../theorem/compatible-idempotent.md) on $(\operatorname{Ind}C,\Phi)$.

*Proof sketch.*
1. $E,\mathcal H,\mathcal V$ have propagation at most $\delta_i\to0$ ([Average propagation](average-propagation.md)); so they are morphisms.
2. With $d=\operatorname{Ind}_0d$ and $\Phi=\operatorname{Ind}_0\phi$, [Sheet shifts multiply](sheet-shift-mul.md) and [Transpose of a sheet shift](sheet-shift-transpose.md) give:
   - $dE-Ed=q^{-1}\sum_g\operatorname{Ind}_g(dA_g-A_gd)$;
   - $E^2-E-d\mathcal H-\mathcal Hd=q^{-2}\sum_{(g,h)}\operatorname{Ind}_{g+h}(A_gA_h-A_{g+h}-dB_{g,h}-B_{g,h}d)$, using $E=q^{-2}\sum_{(g,h)}\operatorname{Ind}_{g+h}A_{g+h}$ (reindex $g\mapsto g+h$ for fixed $h$);
   - $E\Phi-\Phi E^*-d\mathcal V-\mathcal Vd=q^{-1}\sum_g\operatorname{Ind}_g(A_g\phi-\phi A^*_{-g}-dV_g-V_gd)$, using $E^*=q^{-1}\sum_g\operatorname{Ind}_g A^*_{-g}$ (reindex $g\mapsto-g$).
3. Each right side factors through an object of $\mathcal A_Z$ ([Averages of witnesses](average-witness.md), with $I=G_i$ or $G_i^2$), so it is zero in the quotient.

## Sources

- HS paper, Sections 5 and 11.

## Depends on

- [The average](average.md)
- [Compatible homotopy idempotent](../theorem/compatible-idempotent.md)
- [The induced complex](../theorem/induced-complex-poincare.md)

## Proof depends on

- [Average propagation](average-propagation.md)
- [Averages of witnesses](average-witness.md)
- [Sheet shifts multiply](sheet-shift-mul.md)
- [Transpose of a sheet shift](sheet-shift-transpose.md)

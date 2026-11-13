---
article_id: af_9b2816775581a923deff628a
declaration: lemma
origin: bridged
---

# The boundary of a pair has an invariant Lagrangian

For a pair as in [the duality square](pair-duality-square.md), the image $L=f^*H^2(D;\mathbb R)\subset H^2(C;\mathbb R)$ of the [induced map on real cohomology](../real/real-cohomology-map.md) is $G$-invariant and $b_C$-isotropic, and $2\dim L=\dim H^2(C;\mathbb R)$.

*Proof sketch.* Invariance holds because $f$ is equivariant. For isotropy, take cocycles $y,y'$ of $D$. The pair relation $\partial\delta\varphi=f_\%\varphi$ in degree 2, applied to $y$, gives $f\varphi_2f^*y=d\,\delta\varphi_3y$. So $b_C(f^*y,f^*y')=\langle y',d\,\delta\varphi_3y\rangle=\langle d^Ty',\delta\varphi_3y\rangle=0$. For the count, $\varphi_2$ is injective on $H^2(C)$ ([nonsingularity](middle-form-nonsingular.md)). By [the square](pair-duality-square.md), $\dim L=\dim\ker f_*=\dim H_2(C)-\mathrm{rk}\,f_*$. By [the pairing](real-evaluation-pairing.md), $\mathrm{rk}\,f_*=\mathrm{rk}\,f^*=\dim L$ and $\dim H_2(C)=\dim H^2(C)$.

## Sources

- HS paper, Section 3
- OpenAI preprint, 04-lattice.tex lines 55-60

## Depends on

- [The middle form](middle-form.md)
- [Strict Poincaré pair](../../l-theory/base/pairs/poincare-pair.md)
- [The map on real cohomology induced by a chain map](../real/real-cohomology-map.md)

## Proof depends on

- [The duality square](pair-duality-square.md)
- [Middle form nonsingular](middle-form-nonsingular.md)
- [Evaluation is a perfect pairing](real-evaluation-pairing.md)

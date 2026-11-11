---
article_id: af_b15665cb857eaff902d66f49
declaration: lemma
origin: background
statement: formalized
lean: HSP.Cobordant.of_iso
proof: formalized
---

# Isomorphic Poincaré complexes are cobordant

Let $(C,\phi)$ and $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in a duality category $\mathcal B$ and $u:C\to C'$ an isomorphism of complexes with $u_\%\phi=\phi'$. Then $(C,\phi)$ is [cobordant](cobordism.md) to $(C',\phi')$.

*Proof sketch.* Apply [Homotopy-isometric complexes are cobordant](cylinder-cobordism.md) with $\mathcal P$ all objects, $h=u$ and $\chi=0$; the hypothesis $\partial\chi=h_\%\phi-\phi'$ is $0=u_\%\phi-\phi'$.

## Sources

- New: direct

## Depends on

- [Cobordism](cobordism.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)

## Proof depends on

- [Homotopy-isometric complexes are cobordant](cylinder-cobordism.md)

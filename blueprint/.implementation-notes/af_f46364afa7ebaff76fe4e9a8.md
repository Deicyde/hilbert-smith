Lean: `HSP.Compression.scalar_image` (stated, proof open).

Proof plan, following the sketch. (1) `ultL.map_cls` and strictness of `scalarForget` turn the left
side into `cls` of `U'P`; unfold `germ` to `ultL.map q (cls (D, φ))` for the labelled model with
labels `c = f_T` (`labelledModel_poincare`), and push `q` through `cls` the same way. (2) Replace
`D` by `D'` (zero below `i₀`): the identity for `i ≥ i₀` is a unitary isomorphism in `𝒜_𝟏(Sⁿ)`
since morphisms are taken modulo eventual equality. (3) In sphere labels `pr : D' → U'C` and `in`
have propagation `0`; `pr in = 1` and `in pr = 1 - Q`, where `Q` factors with propagation `0`
through discarded cells, whose sphere labels lie in `Z_0` (as in `endpoint` (3)); so `Q = 0` in
`ℬ_{𝟏,Z_0}(Sⁿ)` and `pr` is a unitary isomorphism there, a chain map by `compressed_d`, with
`pr φ pr^* = φ̂`. (4) Homotopy-isometry invariance in `Kar ℬ_{𝟏,Z_0}(Sⁿ)` with `χ = 0` gives
equality in `L^p_N`, then apply `cls`.

Planned names: `HSP.Corner.iteratedCut` for $\Delta_T$, parametrized by the group sequence and a compact $C_p$-space $T$; `HSP.Corner.iteratedCut₁` for $\Delta_{\mathbf 1}$. If the Lean side can treat "without $T$" as $T$ a point, $\Delta_{\mathbf 1}$ is an instance up to the identification $\{\ast\}\times S^n\cong S^n$, but the two component projections differ in their last step (forgetting labels into $\mathcal V_{\mathbf 1}$), so two definitions sharing a recursive helper over $m$ is simpler.

Interface decision 2: this is the single definition of the iterated cut, built from `categories/cuts/cut-boundary.md` exactly as item 3 of the NEEDS section of c1-categories-report.md says. The previous version used the evaluation chapter's inner cuts; those become lemmas computing $d_m$ (requested in the c2-corner report).

Degree bookkeeping: $d_m$ lowers $k$ by one, so the $n$ cuts take $\mathbb L_N$ to $\mathbb L_{N-n}=\mathbb L_4$. For $n=1$ there is no $q$. The recursive helper should take the support set $T\times Y_{m-1}$ as a parameter and rewrite along the cut-flag equalities $A_m\cup B_m=Y_{m-1}$, $A_m\cap B_m=Y_m$; the categories chapter's `cut-boundary` takes $S=A\cup B$ and $Y=A\cap B$ as definitions.

The functor $j$ is described only in a Remark of cut-boundary.md; if $\mathcal A_X$ for $S=X$ is definitionally $\mathcal A_{\mathbf G}(X)$ the map is `id`, otherwise the categories chapter should add a one-line def (requested in the report as optional).

HS paper lines 1150-1165.

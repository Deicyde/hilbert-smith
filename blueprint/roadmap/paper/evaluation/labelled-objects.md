---
article_id: af_6b200fe472dfe897a38cc977
declaration: def
origin: bridged
statement: formalized
lean: HSP.Evaluation.labelledObj, HSP.Evaluation.IsChainModelRep, HSP.Evaluation.labelledPre, HSP.Evaluation.unitMat
---
# Labelled objects

Fix a [local datum](../local-data/chart/local-datum.md), with [chain models](../chain-models/grid/model/chain-model.md) $D_i$, and a continuous map $c:\mathbb T^n\to S^n$ from the [torus](../chain-models/grid/torus.md) to the [round sphere](../corner/round-sphere.md). Work in the [asymptotic category](../categories/asymptotic/asymptotic-category.md) $\mathcal A_{\mathbf 1}(S^n)$ of the [trivial group sequence](../categories/asymptotic/trivial-group-sequence.md).
- For $r\in\mathbb Z$, the *labelled object* $L_c(r)$ is the class of the object $(n_i,x_i)$ with $n_i=\dim(D_i)_r$ and $x_i(b)=c(x_b)$ for the basis cells $b$ of $(D_i)_r$, where $x_b$ is the [torus label](../chain-models/grid/model/chain-model-label.md) of $b$.
- For $r,s\in\mathbb Z$, a morphism $f:L_c(r)\to L_c(s)$ is *represented by* a sequence of rational matrices $m_i\in\mathbb Q^{\dim(D_i)_s\times\dim(D_i)_r}$ if $f=[u]$ for a morphism $u$ of sequences between the underlying objects whose level-$i$ matrix is $m_i$ for every $i$, read as a matrix of [$\mathrm{Free}(\mathbb Q)$](../categories/asymptotic/free-category.md) (the basis $\{1\}\times\{1..n_i\}$ of the trivial group).

## Sources
- HS paper, Section 12 (labellings by a continuous map).

## Depends on
- [Local datum](../local-data/chart/local-datum.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Torus labels of chain-model cells](../chain-models/grid/model/chain-model-label.md)
- [The torus](../chain-models/grid/torus.md)
- [The round sphere](../corner/round-sphere.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [Free category of a finite group](../categories/asymptotic/free-category.md)

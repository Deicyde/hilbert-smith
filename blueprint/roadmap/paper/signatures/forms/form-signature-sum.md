---
article_id: af_ed51bcbea4a6971c67749d3a
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.formSign_sum
---

# Additivity

Let $(W,b,\rho)$ and $(W',b',\rho')$ be as in [the existence lemma](../l-four/signature-splitting-exists.md), for the same $G$. Then $\mathrm{sign}_{b\perp b'}=\mathrm{sign}_b+\mathrm{sign}_{b'}$ on $W\oplus W'$ with the diagonal action, where $(b\perp b')((x,x'),(y,y'))=b(x,y)+b'(x',y')$.

*Proof sketch.* Take splittings of $W$ and $W'$. Their sum is a splitting of $W\oplus W'$. Then use [independence](../l-four/signature-splitting-independence.md) and the trace of a product map.

## Sources

- HS paper, Section 3

## Depends on

- [The equivariant signature](form-signature.md)
- [Invariant signature splittings exist](../l-four/signature-splitting-exists.md)

## Proof depends on

- [Signature splittings](signature-splitting.md)
- [Independence](../l-four/signature-splitting-independence.md)

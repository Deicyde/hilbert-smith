---
article_id: af_5f3ef2fa974a12a18f44ce62
declaration: def
origin: background
statement: formalized
lean: HSP.StructureCx.sum
---

# Sum of structured complexes

$(C,\phi)\oplus(C',\phi')=(C\oplus C',\phi\oplus\phi')$, where $\phi\oplus\phi'=i_\%\phi+i'_\%\phi'$ for the inclusions $i:C\to C\oplus C'$ and $i':C'\to C\oplus C'$ ([pushforward](structure-push.md)). So $(\phi\oplus\phi')_r$ is $\phi_r\oplus\phi'_r$ precomposed with the canonical isomorphism $(C_{n-r}\oplus C'_{n-r})^*\cong C^*_{n-r}\oplus C'^*_{n-r}$, whose components are the duals of the inclusions.

## Sources

- [Ranicki 1980 I, §1](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Structure complex](structure-complex.md)
- [Pushforward of structures](structure-push.md)

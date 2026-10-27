# Fast kernel grinding certificates

`FastCompress.lean` proves an unrolled fixed-word BLAKE2s compression equivalent to the executable private compression. `FastHash96.lean` proves the two-block (96-byte input) hash bridge used by XMSS randomizer and encoding calls. `GrindingSupport.lean` rewrites the existing `randomizer` and `wotsEncode` definitions through that bridge; runtime definitions and KAT statements remain unchanged.

The files use only `propext`, `Classical.choice`, and `Quot.sound` transitively. No native evaluation, axioms, or sorry proofs are used.

# Fast kernel grinding certificates

`FastCompress.lean` proves an unrolled fixed-word BLAKE2s compression equivalent to the executable private compression. `FastHash96.lean` proves the two-block (96-byte input) hash bridge used by XMSS randomizer and encoding calls. `GrindingSupport.lean` rewrites the existing `randomizer` and `wotsEncode` definitions through that bridge; runtime definitions and KAT statements remain unchanged.

The files use only `propext`, `Classical.choice`, and `Quot.sound` transitively. No native evaluation, axioms, or sorry proofs are used.

## Portable worker protocol

Repository: `https://github.com/Th0rgal/EthLib.git`, branch `astra/xmss-fast-grinding`.

1. Use the exact `lean-toolchain` in the checkout (v4.29.1).
2. Fetch package dependencies and mathlib cache, then `lake build EthLib.Cryptography.Proofs.Xmss.GrindingSupport`.
3. Generate one batch with `python3 tools/gen_grinding_batch.py START COUNT`; default output is `EthLib/Cryptography/Proofs/Xmss/GrindingBatches/`.
4. Check the generated file with `lake env lean -DwarningAsError=true -o OUTPUT.olean FILE.lean`. Do not count a range as checked without exit 0.
5. Record source SHA256, command, exit code, elapsed seconds, and peak RSS. Limit initial concurrency to four batches on a 32 GB VM; increase only after measuring available RAM.
6. Each theorem `no_early_START_END` proves the original executable rejection for every `START <= t < END`. The helper `grindingSeed` has exactly the original `exampleSeed` definition, so integration is by definitional equality.

The Python generator is untrusted certificate production: every randomizer and rejection is independently checked by Lean's kernel. It does not alter runtime code or the original theorem statements. Preserve checked sources and logs; generated `.olean` files are optional transport caches, not evidence by themselves.

# mmr changelog

## 0.1.0

- First version.
  - `Peaks`: the core. Peaks with a counter; `carry`, `close`, `foldBranch`; adding leaves from Blobs, pairs of Blobs, hashers and messages; saving, exporting and restoring the peaks; the table of zero-subtree roots.
  - Presets `Bitcoin`, `Bagged` and `Ssz`, each with roots, inclusion-proof verification and a chunk verifier.
  - `Chunks`: verification of a list against a known root, chunk by chunk.
  - `Prove`: proofs from all the leaves.

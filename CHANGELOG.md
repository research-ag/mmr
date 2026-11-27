# mmr changelog

The shapes of the record types that a canister can store (`Peaks.Peaks`, `Chunks.Verifier`) are part of the interface. A change to one of them is listed as **Breaking (stored state)**.

## 0.1.0

- First version.
  - `Peaks`: the core. Peaks with a counter and the tree's rules (`double`, `fill`); `carry`, `close`, `foldBranch`; adding leaves from Blobs, pairs of Blobs, runs of Blobs, hashers and messages; saving, exporting and restoring the peaks; the table of zero-subtree roots.
  - Presets `Bitcoin`, `Bagged` and `ZeroPadded`: constructors of trees with their format's rules, one-shot roots, inclusion-proof verification, a chunk verifier (`verifier`, and `verifierOn` for a tree of the caller's) and the whole tree for the prover (`merkleTree`).
  - `Chunks`: verification of a list against a known root, chunk by chunk, with its own tree or on a tree of the caller's. A rejected chunk makes the verifier fail.
  - `MerkleTree`: the whole tree with its rules, and the proofs computed from it (`branch`, `rightPeaks`).
  - A tree padded to a fixed depth d that holds more than 2^d leaves has no root: `Peaks.close` (and so `root`) and `MerkleTree.build` trap on it.

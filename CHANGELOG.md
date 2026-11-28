# mmr changelog

The shapes of the record types that a canister can store (`Peaks.Tree`, `Chunks.Verifier`) are part of the interface. A change to one of them is listed as **Breaking (stored state)**.

## 0.1.0

- First version.
  - `Peaks`: the core. Peaks with a counter and the tree's rules (`double`, `fill`); `carry`, `close`, `foldBranch`, `verifyBranch`; adding leaves from Blobs, pairs of Blobs, runs of Blobs, hashers and messages; saving, exporting and restoring the peaks, between trees of the same rules (`sameRules`); the table of zero-subtree roots.
  - Presets `Bitcoin`, `Bagged` and `ZeroPadded`: constructors of trees with their format's rules, one-shot roots, inclusion-proof verification, a chunk verifier (`verifier`, and `verifierOn` for a tree of the caller's) and the whole tree for the prover (`merkleTree`).
  - `Chunks`: verification of a list against a known root, chunk by chunk, on a tree that takes its rules from the tree (`onTree`); the presets make one (`verifier`) or take the caller's (`verifierOn`). A rejected chunk makes the verifier fail.
  - `MerkleTree`: the whole tree with its rules, and the proofs computed from it (`branch`, `rightPeaks`).
  - A tree padded to depth d that holds more than 2^d leaves has no root: `Peaks.close` (and so `root`) and `MerkleTree.build` trap on it. Its `capacity` is 2^d, so `load` and the chunk verifier refuse more leaves without a trap.
  - The padding depth is at most 62: `Peaks.new` and `withDepth` trap on a deeper `#zeros` fill, or one whose table is too short, and `close` on a record made by hand with one.
  - A chunk verifier on a tree of d + 2 hashers takes up to 2^d leaves: make its tree with `withDepth(d)`.

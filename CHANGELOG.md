# mmr changelog

The shapes of the record types that a canister can store (`Peaks.Peaks`, `Chunks.Verifier`, the presets' `Tree`) are part of the interface. A change to one of them is listed as **Breaking (stored state)**.

## 0.1.0

- First version.
  - `Peaks`: the core. Peaks with a counter; `carry`, `close`, `foldBranch`; adding leaves from Blobs, pairs of Blobs, runs of Blobs, hashers and messages; saving, exporting and restoring the peaks; the table of zero-subtree roots.
  - Presets `Bitcoin`, `Bagged` and `Ssz`, each with roots, inclusion-proof verification and a chunk verifier (`verifier`, and `verifierOn` for a tree of the caller's).
  - `Chunks`: verification of a list against a known root, chunk by chunk, with its own tree and a backup or on a tree of the caller's without one.
  - `Prove`: proofs from all the leaves.

# mmr

Merkle mountain ranges over SHA-256 for Motoko: append-only Merkle trees that keep only their peaks, with roots, inclusion proofs and chunked verification, and no heap allocation while hashing.

The package is built on the `Hasher` of [`sha2`](https://mops.one/sha2), which combines two 32-byte hashes without allocating.
A tree of n leaves is held as at most log2(n) + 2 hashers, whatever n is.

## What is in it

| Module    | What it is                                                                                            |
| --------- | ----------------------------------------------------------------------------------------------------- |
| `Peaks`   | The core: the peaks with their counter, and the operations every tree format shares                   |
| `Bitcoin` | Preset: Bitcoin's transaction tree (double SHA-256, the last node of an odd level paired with itself) |
| `Bagged`  | Preset: the tree shape of RFC 6962 without its prefix bytes (AWS Glacier tree hash, OpenTimestamps)   |
| `Ssz`     | Preset: zero-padded trees of fixed depth (SSZ of Ethereum's consensus layer, the deposit contract)    |
| `Chunks`  | Verification of a long list against a known root, chunk by chunk                                      |
| `Prove`   | The prover: proofs computed from all the leaves                                                       |

Every node is the SHA-256, single or double, of the 64 bytes of its two children.
There is no prefix and no domain separation, so the hashes of a transparency log (RFC 6962 proper), of ICP hash trees and of Keccak- or BLAKE-based chains are out of scope.

## Install

```bash
mops add mmr
```

## The presets

### Bitcoin

```motoko
import Bitcoin "mo:mmr/Bitcoin";

// In one shot. Traps on a mutated list (see below).
let root = Bitcoin.merkleRoot(txids);

// Or as the transactions arrive.
let tree = Bitcoin.new(10_000);
for (txid in txids.values()) tree.add(txid);
let sameRoot = tree.root();

// A Merkle branch: is this txid the transaction at this position?
let ok = Bitcoin.verifyBranch(txid, index, branch, root);
```

Txids and roots are in Bitcoin's internal byte order, the reverse of what block explorers display.

### Bagged

```motoko
import Bagged "mo:mmr/Bagged";
import Sha256 "mo:sha2/Sha256";

let tree = Bagged.new(1_000_000);
let digest = Sha256.new();
for (chunk in chunks.values()) tree.addMessage(digest, chunk); // the leaf is SHA-256(chunk)
let root = tree.root();

let ok = Bagged.verifyInclusion(leaf, index, size, path, root);
```

### Zero-padded (SSZ)

```motoko
import Ssz "mo:mmr/Ssz";

let tree = Ssz.new(32); // 2^32 places, as the deposit contract
for (chunk in chunks.values()) tree.add(chunk);
let root = tree.root(); // padded with zero chunks
let listRoot = tree.rootWithLength(); // with the number of chunks mixed in

let ok = Ssz.verifyBranch(leaf, index, branch, root); // is_valid_merkle_branch
```

## Verifying in chunks

A canister that receives a long list in several calls can check each chunk when it arrives, against nothing but the root, and reject a bad chunk at once.

```motoko
import Bitcoin "mo:mmr/Bitcoin";
import Chunks "mo:mmr/Chunks";

let verifier = Bitcoin.verifier(root, 14); // at most 2^14 transactions

// per call: the next txids, and the uploader's proof for the rest
if (not verifier.verifyChunk(chunk, proof)) { /* reject the call */ };
if (verifier.complete()) { /* that was the last chunk */ };
```

The proof that goes with a chunk is the list of peaks to the right of the chunk's last leaf; the last chunk has an empty one.
The uploader computes them with `Prove.rightPeaks`.
A rejected chunk makes the verifier `failed`: it accepts nothing more. Verification allocates nothing.

Each chunk costs its leaves plus one hash per level of the tree, so this suits a few large chunks better than many small ones.

A canister that traps on a rejected chunk can keep a single tree for all its uploads:

```motoko
import Peaks "mo:mmr/Peaks";

let tree = Peaks.withDepth(14, true); // once: at most 2^14 leaves, double SHA-256

// per upload: a verifier on that tree
let verifier = Bitcoin.verifierOn(root, tree);
if (not verifier.verifyChunk(chunk, proof)) { /* trap */ };
```

`Bagged` and `Ssz` have a `verifierOn` as well; `Chunks.onTree` is the general form, with the rules of the tree as arguments.

## The core

The presets are thin. To build another tree format, use `Peaks` directly.

- **The structure.** Slot k of the pool holds the root of the perfect subtree ("peak") of 2^k leaves, exactly when bit k of the leaf count is set. One more hasher is a spare for the node being worked on.
- **`carry(height)`** inserts the node in the spare as a peak of that height and merges upward while the count has a 1-bit: the increment of a binary counter. `add` is a carry at height 0, `addPair` fuses two leaves straight from their Blobs and carries at height 1, and the root of a whole subtree can be carried at its height. `addAll` adds a run of leaves in pairs, from any count.
- **`close(proof, fill, checked)`** computes a root without changing the peaks. Going up from the lowest peak, the node in hand meets a peak of the tree on its left where the count has a 1-bit, else the next entry of `proof` on its right, else what `fill` says: nothing (`#skip`, bagging), itself (`#copy`, Bitcoin), or the all-zero subtree of its height (`#zeros`). With an empty proof that is the root; with the peaks of the rest it verifies a prefix.
- **`foldBranch`** folds a node up a list of siblings, for inclusion proofs.
- **`copy`, `toBlobs`, `load`** save, export and restore the peaks.

`carryChecked`, `addChecked` and `close` with `checked` reject two equal siblings, which is what the Bitcoin preset uses against mutated lists.

## What a Merkle root does not tell you

These trees have no domain separation. That is how the formats are defined, and it has consequences the package cannot remove.

- **Leaves and inner nodes look alike.** The nodes of any whole level of a tree verify as a shorter list of leaves with the same root. In Bitcoin this is CVE-2017-12842: the header commits to neither the depth nor the transaction count. An application that needs to know that its leaves are leaves must fix the depth another way, for example by taking the first transaction in full and checking that it is not 64 bytes long.
- **Bitcoin's duplication (CVE-2012-2459).** A list that writes out a duplicated tail has the same root as the shorter one: `[1,2,3]` and `[1,2,3,3]`. `Bitcoin.merkleRoot` traps on such a list, and the checked functions and the chunk verifier reject equal siblings. The plain `add` and `root` hash what they are given.
- **Bagged roots do not commit to the leaf count.** `Bagged.verifyInclusion` takes the tree size as a parameter for that reason, and the caller has to know it.
- **Zero padding hides trailing zeros.** A last leaf of 32 zero bytes cannot be told from padding. Where the length varies, mix it in (`Ssz.rootWithLength`).

## Stored state

`Peaks.Peaks`, `Chunks.Verifier` and the presets' `Tree` types are plain records without functions, so a canister can keep them in stable variables across upgrades.
Their shapes are therefore part of the package's interface:

- A change to a field of one of these types is a breaking change. The CHANGELOG marks it as such, and it comes with a new minor version while the package is at 0.x.
- A canister that stores such a record then needs a migration when it upgrades to the new version. With enhanced orthogonal persistence, Motoko refuses an upgrade to incompatible stable types, so a missing migration shows as a failed upgrade and not as lost state.
- The records contain the `Hasher` of `sha2`, a `[var Nat16]` of 16 half-words. A `sha2` release that changed that representation would change these types too.

## Performance

Measured with moc 2.2.4 and wasm-opt, in instructions, for random 32-byte leaves:

| Operation                                | 1,000 leaves | 8,000 leaves | per leaf |
| ---------------------------------------- | -----------: | -----------: | -------: |
| `Bitcoin.merkleRoot`                     |   24,400,000 |  195,000,000 |   24,400 |
| Bitcoin, `add` leaf by leaf, then `root` |   25,300,000 |  202,100,000 |   25,300 |
| the same with `addChecked`               |   25,300,000 |  202,500,000 |   25,300 |
| `Bagged.merkleRoot`                      |   16,100,000 |  128,600,000 |   16,100 |
| bagged, `add` leaf by leaf, then `root`  |   16,900,000 |  135,700,000 |   17,000 |
| zero-padded to depth 20, `add`, `root`   |   17,100,000 |  135,800,000 |   17,000 |
| Bitcoin, verified in 3 chunks            |   25,100,000 |  197,200,000 |   24,600 |
| bagged, verified in 3 chunks             |   16,500,000 |  130,100,000 |   16,300 |

A double-SHA node is three SHA-256 compressions and a single-SHA node two, and a tree has about one node per leaf.
Adding in pairs saves about 900 instructions per leaf, because the two leaves are read straight from their Blobs.
The one-shot roots and the chunk verifier add in pairs.
Nothing allocates per leaf; a root allocates its `Blob`.

Run the benchmark with `mops bench`.

## Development

```bash
mops install
mops test
mops bench
mops format
```

The tests compare every tree with a straightforward reference written with the plain `Sha256` digest, with vectors from an independent implementation, and with known constants of Bitcoin and of Ethereum's consensus layer. A second test file checks the allocation claims.

## License

Apache-2.0

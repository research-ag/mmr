# mmr

Merkle mountain ranges over SHA-256 for Motoko: append-only Merkle trees that keep only their peaks, with roots, inclusion proofs and chunked verification, and no heap allocation while hashing.

The package is built on the `Hasher` of [`sha2`](https://mops.one/sha2), which combines two 32-byte hashes without allocating.
A tree of n leaves is held as at most log2(n) + 2 hashers, whatever n is.

## What is in it

| Module       | What it is                                                                                            |
| ------------ | ----------------------------------------------------------------------------------------------------- |
| `Peaks`      | The core: the tree as its peaks, counter and rules, and the operations every tree format shares       |
| `Bitcoin`    | Preset: Bitcoin's transaction tree (double SHA-256, the last node of an odd level paired with itself) |
| `Bagged`     | Preset: the tree shape of RFC 6962 without its prefix bytes (AWS Glacier tree hash, OpenTimestamps)   |
| `ZeroPadded` | Preset: zero-padded trees of fixed depth (SSZ of Ethereum's consensus layer, the deposit contract)    |
| `Chunks`     | Verification of a long list against a known root, chunk by chunk                                      |
| `MerkleTree` | The whole tree, every level of it: the prover's side, for proofs computed from all the leaves         |

Every node is the SHA-256, single or double, of the 64 bytes of its two children.
There is no prefix and no domain separation, so the hashes of a transparency log (RFC 6962 proper), of ICP hash trees and of Keccak- or BLAKE-based chains are out of scope.

## The formats in brief

A Merkle tree commits to a list of **leaves**, 32-byte hashes of the data (transaction ids, chunks of a file).
Each **node** is the hash of its two children, `H(left ++ right)`, level by level, up to a single node, the **root**.
Whoever knows the root can check data against it without seeing the rest:

- An **inclusion proof** (or **branch**) shows that one leaf is at a given position: the siblings of the nodes on its way up to the root, lowest first. The check hashes one node per level.
- A **chunk proof** shows that a run of leaves is the beginning of the list: the roots of the subtrees that cover the rest, the **peaks to the right** of the run. Each chunk of a long upload can be checked this way as it arrives.

A tree that is built as the leaves arrive needs to keep only its **peaks**: the roots of the perfect subtrees that cover the leaves so far, one of 2^k leaves for every 1-bit k of the count (11 leaves: subtrees of 8, 2 and 1). That is a Merkle mountain range, and it is what `Peaks` holds: about log2(n) hashes, whatever n is.

The formats this package implements differ only where a level has an odd number of nodes. With five leaves, and `xy` for `H(x ++ y)`:

```
           Bitcoin                  Bagged                 Zero-padded, depth 3
level 0    a  b  c  d  e            a  b  c  d  e          a  b  c  d  e  0  0  0
level 1     ab   cd   ee             ab   cd   e            ab   cd   e0   00
level 2       abcd   eeee              abcd    e              abcd     e000
root         H(abcd ++ eeee)          H(abcd ++ e)           H(abcd ++ e000)
```

| Format      | A node is     | The last node of an odd level                                    | Used by                                                                | What the root does not pin down                   |
| ----------- | ------------- | ---------------------------------------------------------------- | ---------------------------------------------------------------------- | ------------------------------------------------- |
| Bitcoin     | SHA-256 twice | is paired with itself                                            | Bitcoin's block header and its forks, merged mining, Stratum           | the list: `[a, b, c]` and `[a, b, c, c]` share it |
| Bagged      | SHA-256       | moves up unchanged                                               | RFC 6962 (without its prefix bytes), AWS Glacier, OpenTimestamps       | the number of leaves                              |
| Zero-padded | SHA-256       | is paired with an all-zero subtree, up to a fixed 2^depth places | SSZ of Ethereum's consensus layer, the deposit contract, BitTorrent v2 | a trailing leaf of zeros; SSZ mixes the length in |

In the code, the rule for the odd node is a `Peaks.Fill`: `#copy`, `#skip` and `#zeros`.
It also shapes the inclusion proofs: Bitcoin's and zero-padded branches have one sibling per level, with the copy or the zero subtree written out, and a bagged path leaves out the levels at which the node has no sibling.

## Install

```bash
mops add mmr
```

## The presets

### Bitcoin

A preset makes trees with its format's rules, and has the functions particular to the format.
The tree itself is a `Peaks.Tree`, whatever the format, and is used with the functions of `Peaks`, so that module is imported as well.

```motoko
import Bitcoin "mo:mmr/Bitcoin";
import MerkleTree "mo:mmr/MerkleTree";
import Peaks "mo:mmr/Peaks";

// In one shot. Traps on a mutated list (see below).
let root = Bitcoin.merkleRoot(txids);

// Or as the transactions arrive.
let tree = Bitcoin.new(10_000);
for (txid in txids.values()) tree.add(txid);
let sameRoot = tree.root();

// A Merkle branch, from the whole tree: is this txid the transaction at this position?
let branch = Bitcoin.merkleTree(txids).branch(index);
let ok = Bitcoin.verifyBranch(txid, index, branch, root);
```

Txids and roots are in Bitcoin's internal byte order, the reverse of what block explorers display.

### Bagged

```motoko
import Bagged "mo:mmr/Bagged";
import MerkleTree "mo:mmr/MerkleTree";
import Peaks "mo:mmr/Peaks";
import Sha256 "mo:sha2/Sha256";

let tree = Bagged.new(1_000_000);
let digest = Sha256.new();
for (chunk in chunks.values()) tree.addMessage(digest, chunk); // the leaf is SHA-256(chunk)
let root = tree.root();

let path = Bagged.merkleTree(leaves).branch(index);
let ok = Bagged.verifyInclusion(leaf, index, size, path, root);
```

### Zero-padded

```motoko
import ZeroPadded "mo:mmr/ZeroPadded";
import MerkleTree "mo:mmr/MerkleTree";
import Peaks "mo:mmr/Peaks";

let tree = ZeroPadded.new(32); // 2^32 places, as the deposit contract
for (chunk in chunks.values()) tree.add(chunk);
let root = tree.root(); // padded with zero chunks
let listRoot = tree.rootWithLength(); // with the number of chunks mixed in

let branch = ZeroPadded.merkleTree(chunks, 32).branch(index);
let ok = ZeroPadded.verifyBranch(leaf, index, branch, root); // is_valid_merkle_branch
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
The uploader computes them from the whole tree, with `MerkleTree.rightPeaks`: `Bitcoin.merkleTree(txids).rightPeaks(m)` for a chunk that ends before leaf `m`.
A rejected chunk makes the verifier `failed`: it accepts nothing more. Verification allocates nothing.

Each chunk costs its leaves plus one hash per level of the tree, so this suits a few large chunks better than many small ones.

A canister that traps on a rejected chunk can keep a single tree for all its uploads:

```motoko
let tree = Bitcoin.withDepth(14); // once: at most 2^14 transactions

// per upload: a verifier on that tree
let verifier = Bitcoin.verifierOn(root, tree);
if (not verifier.verifyChunk(chunk, proof)) { /* trap */ };
```

`Bagged` and `ZeroPadded` have a `verifierOn` as well, which traps on a tree of another format; `Chunks.onTree` is the general form, for a tree of any format.

## The core

The presets are thin. To build another tree format, use `Peaks` directly.

- **The structure.** Slot k of the pool holds the root of the perfect subtree ("peak") of 2^k leaves, exactly when bit k of the leaf count is set. One more hasher is a spare for the node being worked on. The record also holds the tree's two rules: `double` (SHA-256 once or twice per node) and `fill` (the odd node). A preset is a constructor that chooses them: `Bitcoin.new(n)` is `Peaks.new(n, true, #copy)`.
- **`carry(height)`** inserts the node in the spare as a peak of that height and merges upward while the count has a 1-bit: the increment of a binary counter. `add` is a carry at height 0, `addPair` fuses two leaves straight from their Blobs and carries at height 1, and the root of a whole subtree can be carried at its height. `addAll` adds a run of leaves in pairs, from any count.
- **`close(proof, checked)`** computes a root without changing the peaks. Going up from the lowest peak, the node in hand meets a peak of the tree on its left where the count has a 1-bit, else the next entry of `proof` on its right, else what the tree's `fill` says: nothing (`#skip`, bagging), itself (`#copy`, Bitcoin), or the all-zero subtree of its height (`#zeros`). With an empty proof that is the root; with the peaks of the rest it verifies a prefix.
- **`foldBranch`** folds a node up a list of siblings, and **`verifyBranch`** checks an inclusion proof with one sibling per level (the presets' `verifyBranch` for Bitcoin and zero-padded trees).
- **`copy`, `toBlobs`, `load`** save, export and restore the peaks. `copy` only goes between trees of the same rules (`sameRules`), and `load` refuses more leaves than the tree's `capacity`, which for a zero-padded tree is its number of places.

`carryChecked`, `addChecked` and `close` with `checked` reject two equal siblings, which is what the Bitcoin preset uses against mutated lists.

## What a Merkle root does not tell you

These trees have no domain separation. That is how the formats are defined, and it has consequences the package cannot remove.

- **Leaves and inner nodes look alike.** The nodes of any whole level of a tree verify as a shorter list of leaves with the same root. In Bitcoin this is CVE-2017-12842: the header commits to neither the depth nor the transaction count. An application that needs to know that its leaves are leaves must fix the depth another way, for example by taking the first transaction in full and checking that it is not 64 bytes long.
- **Bitcoin's duplication (CVE-2012-2459).** A list that writes out a duplicated tail has the same root as the shorter one: `[1,2,3]` and `[1,2,3,3]`. `Bitcoin.merkleRoot` traps on such a list, and the checked functions and the chunk verifier reject equal siblings. The plain `add` and `root` hash what they are given.
- **Bagged roots do not commit to the leaf count.** `Bagged.verifyInclusion` takes the tree size as a parameter for that reason, and the caller has to know it.
- **Zero padding hides trailing zeros.** A last leaf of 32 zero bytes cannot be told from padding. Where the length varies, mix it in (`ZeroPadded.rootWithLength`).
- **A zero-padded tree has no root beyond its places.** `ZeroPadded.new(d)` accepts more than 2^d chunks, since adding checks nothing, but taking its root then traps. The chunk verifier rejects such a chunk instead.

## Stored state

`Peaks.Tree` (the tree of every preset) and `Chunks.Verifier` are plain records without functions, so a canister can keep them in stable variables across upgrades.
Their shapes are therefore part of the package's interface:

- A change to a field of one of these types is a breaking change. The CHANGELOG marks it as such, and it comes with a new minor version while the package is at 0.x.
- A canister that stores such a record then needs a migration when it upgrades to the new version. With enhanced orthogonal persistence, Motoko refuses an upgrade to incompatible stable types, so a missing migration shows as a failed upgrade and not as lost state.
- The records contain the `Hasher` of `sha2`, a `[var Nat16]` of 16 half-words. A `sha2` release that changed that representation would change these types too.

## Performance

Measured with moc 2.2.5 and wasm-opt 133, in instructions, for random 32-byte leaves; the column per leaf is from the 8,000 leaves:

| Operation                                | 1,000 leaves | 8,000 leaves | per leaf |
| ---------------------------------------- | -----------: | -----------: | -------: |
| `Bitcoin.merkleRoot`                     |   25,500,000 |  203,800,000 |   25,500 |
| Bitcoin, `add` leaf by leaf, then `root` |   26,500,000 |  210,700,000 |   26,300 |
| the same with `addChecked`               |   26,500,000 |  211,200,000 |   26,400 |
| `Bagged.merkleRoot`                      |   17,400,000 |  139,600,000 |   17,500 |
| bagged, `add` leaf by leaf, then `root`  |   18,400,000 |  146,600,000 |   18,300 |
| zero-padded to depth 20, `add`, `root`   |   18,600,000 |  146,700,000 |   18,300 |
| Bitcoin, verified in 3 chunks            |   26,700,000 |  206,700,000 |   25,800 |
| bagged, verified in 3 chunks             |   18,400,000 |  142,000,000 |   17,700 |

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

The tests compare every tree with a straightforward reference written with the plain `Sha256` digest, over generated leaves and for the zero hashes of SSZ. `test/readme.test.mo` runs the examples of this README. The tests in `test/allocation/` check the allocation claims, and those in `test/traps/` run in a replica, to check that a call traps.

## License

Apache-2.0

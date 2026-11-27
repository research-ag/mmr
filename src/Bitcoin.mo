/// Preset: BITCOIN's Merkle tree over transaction ids. Every node is a double
/// SHA-256, and where a level has an odd number of nodes the last one is
/// paired with itself. The same tree is used by Bitcoin's forks, by merged
/// mining and by the Stratum protocol.
///
/// Txids, roots and proofs are in Bitcoin's INTERNAL byte order, the raw
/// output of the double SHA-256. Block explorers and RPC display them
/// byte-reversed.
///
/// === Mutated lists (CVE-2012-2459) ===
///
/// Pairing the last node with itself means that distinct lists can have the
/// same root: `[1,2,3]` and `[1,2,3,3]`, or `[1..6]` and `[1,2,3,4,5,6,5,6]`.
/// A root alone does not pin down the list. There are two defences here:
///
///   - `mutated` tests a complete list before any hashing. `merkleRoot` runs
///     it and traps on a flagged list.
///   - The checked functions (`addChecked`, `verifier`) reject two EQUAL
///     SIBLINGS wherever they would be combined. A valid block never has
///     them, and a mutated list always does. This is what Bitcoin Core does,
///     and it needs no view of the whole list.
///
/// The plain `add` and `root` hash what they are given.
///
/// === Leaves and inner nodes (CVE-2017-12842) ===
///
/// The tree does not mark leaves apart from inner nodes, and the block header
/// commits to neither the depth nor the transaction count. The nodes of any
/// whole level therefore verify as a shorter list of "txids", and a 64-byte
/// transaction can pose as an inner node. Nothing in this module can tell.
/// An application that needs the difference must fix the depth by other
/// means: for example by taking the first transaction, the coinbase, in full
/// and checking that it is not 64 bytes long.

import Hasher "mo:sha2/Hasher/Sha256";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import Chunks "Chunks";
import Peaks "Peaks";
import Prove "Prove";

module {
  /// A Bitcoin tree: `Peaks` with double SHA-256. The `kind` field only
  /// keeps the trees of different presets apart for the type checker; the
  /// core functions are reached through `peaks`. A static record that can be
  /// declared `stable`; its shape is part of the package's interface.
  public type Tree = { peaks : Peaks.Peaks; kind : { #bitcoin } };

  /// An empty tree with room for at least `maxLeaves` txids.
  public func new(maxLeaves : Nat) : Tree = {
    peaks = Peaks.new(maxLeaves, true);
    kind = #bitcoin;
  };

  /// Add a txid (32 bytes, internal byte order).
  public func add(self : Tree, txid : Blob) = self.peaks.add(txid);

  /// Add a txid, rejecting equal siblings: `false`, and the tree unchanged,
  /// if two equal nodes would be merged.
  public func addChecked(self : Tree, txid : Blob) : Bool = self.peaks.addChecked(txid);

  /// The number of txids added so far.
  public func count(self : Tree) : Nat64 = self.peaks.count;

  /// The Merkle root of the txids added so far (at least one). The tree is
  /// left unchanged.
  public func root(self : Tree) : Blob = self.peaks.root(#copy);

  /// Whether `leaves` may be a MUTATED list: true if the last leaf equals the
  /// one 1, 2, 4, 8, ... places before it. That holds for every list that
  /// shares its root with another one by writing out a duplicated tail, and
  /// otherwise only for lists that repeat a leaf, which a valid block never
  /// does. At most log2(n) comparisons, no hashing, no allocation.
  public func mutated(leaves : [Blob]) : Bool {
    let n = leaves.size();
    var back = 1;
    while (back < n) {
      if (leaves[n - 1 - back] == leaves[n - 1]) return true;
      back *= 2;
    };
    false;
  };

  /// The Merkle root of a complete list of txids (at least one), in one
  /// shot. Traps if the list is flagged by `mutated`.
  public func merkleRoot(txids : [Blob]) : Blob {
    let n = txids.size();
    assert n >= 1;
    if (n == 1) {
      // A block with only its coinbase: the root is the txid itself.
      assert txids[0].size() == 32;
      return txids[0];
    };
    if (mutated(txids)) Runtime.trap("mmr: mutated transaction list (CVE-2012-2459)");
    let peaks = Peaks.new(n, true);
    ignore peaks.addAll(txids, 0, n, false);
    peaks.root(#copy);
  };

  /// Verify a MERKLE BRANCH: that `txid` is the transaction at position
  /// `index` of a block with Merkle root `root`. `branch` holds one sibling
  /// hash per level, lowest first, with the duplicate written out where
  /// Bitcoin pairs a node with itself. That is what `Prove.branch` gives
  /// with `#copy`, and what Stratum sends for the coinbase (index 0). It is
  /// not the `merkleblock` of `gettxoutproof`, a partial tree with flag bits
  /// that has to be decoded first. A malformed branch gives `false`.
  /// See the note on leaves and inner nodes above.
  public func verifyBranch(txid : Blob, index : Nat, branch : [Blob], root : Blob) : Bool {
    if (txid.size() != 32 or branch.size() > 62) return false;
    var j = 0;
    while (j < branch.size()) {
      if (branch[j].size() != 32) return false;
      j += 1;
    };
    // The index must lie within a tree of that depth.
    if (index > 2305843009213693951) return false; // 2^61 - 1: the largest bound that compares without allocating
    let position = index.toNat64();
    if ((position >> branch.size().toNat64()) != 0) return false;
    let node = Hasher.new();
    node.loadBlob32(txid);
    Peaks.foldBranch(node, position, branch, true);
    node.equalsBlob32(root);
  };

  /// A chunk verifier for the block with Merkle root `root` and at most
  /// 2^maxDepth transactions, with the check for equal siblings: proofs must
  /// be minimal, the last chunk is recognised by its empty proof, and mutated
  /// lists are rejected. See `Chunks`.
  public func verifier(root : Blob, maxDepth : Nat) : Chunks.Verifier = Chunks.new(root, maxDepth, true, #copy, true);

  /// The same verifier on a tree that the caller owns: the
  /// tree is emptied, nothing is allocated but the verifier's record, and a
  /// rejected chunk fails the verifier (see `Chunks.onTree`). For a canister
  /// that traps on a rejected chunk and keeps one tree for all its blocks. A
  /// tree made by `Peaks.withDepth(d, true)` verifies up to 2^d transactions.
  /// Traps if the tree does not use double SHA-256.
  public func verifierOn(root : Blob, tree : Peaks.Peaks) : Chunks.Verifier {
    assert tree.double;
    Chunks.onTree(root, tree, #copy, true);
  };

  /// The levels of the tree over `txids`, for `Prove.rightPeaks` (the proofs
  /// of the chunk verifier) and `Prove.branch` (Merkle branches).
  public func levels(txids : [Blob]) : [[Blob]] = Prove.levels(txids, #copy, true);
};

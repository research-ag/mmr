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
///   - The checked functions (`Peaks.addChecked`, `verifier`) reject two EQUAL
///     SIBLINGS wherever they would be combined. A valid block never has
///     them, and a mutated list always does. This is what Bitcoin Core does,
///     and it needs no view of the whole list.
///
/// The plain `Peaks.add` and `Peaks.root` hash what they are given.
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

import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import Chunks "Chunks";
import Peaks "Peaks";
import MerkleTree "MerkleTree";

module {
  /// An empty Bitcoin tree with room for at least `maxLeaves` txids: `Peaks`
  /// with double SHA-256 and the `#copy` fill. Txids are added, and the root
  /// taken, with the functions of `Peaks` (`add`, `addChecked`, `root`).
  public func new(maxLeaves : Nat) : Peaks.Tree = Peaks.new(maxLeaves, true, #copy);

  /// An empty Bitcoin tree with room for 2^depth txids (depth at most 61).
  public func withDepth(depth : Nat) : Peaks.Tree = Peaks.withDepth(depth, true, #copy);

  /// Whether `tree` has Bitcoin's rules: double SHA-256 and the `#copy` fill.
  public func isBitcoin(tree : Peaks.Tree) : Bool = tree.double and tree.fill == #copy;

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
    let tree = new(n);
    ignore tree.addAll(txids, 0, n, false);
    tree.root();
  };

  /// Verify a MERKLE BRANCH: that `txid` is the transaction at position
  /// `index` of a block with Merkle root `root`. `branch` holds one sibling
  /// hash per level, lowest first, with the duplicate written out where
  /// Bitcoin pairs a node with itself, and at most 61 levels. That is what
  /// `MerkleTree.branch` gives for a Bitcoin tree, and what Stratum sends for
  /// the coinbase (index 0). It is not the `merkleblock` of `gettxoutproof`,
  /// a partial tree with flag bits that has to be decoded first. A malformed
  /// branch gives `false`. See the note on leaves and inner nodes above.
  public func verifyBranch(txid : Blob, index : Nat, branch : [Blob], root : Blob) : Bool =
    Peaks.verifyBranch(txid, index, branch, root, true);

  /// A chunk verifier for the block with Merkle root `root` and at most
  /// 2^maxDepth transactions, with the check for equal siblings: proofs must
  /// be minimal, the last chunk is recognised by its empty proof, and mutated
  /// lists are rejected. See `Chunks`.
  public func verifier(root : Blob, maxDepth : Nat) : Chunks.Verifier = Chunks.onTree(root, withDepth(maxDepth), true);

  /// The same verifier on a tree that the caller owns: the tree is emptied,
  /// nothing is allocated but the verifier's record, and a rejected chunk
  /// fails the verifier (see `Chunks.onTree`). For a canister that traps on
  /// a rejected chunk and keeps one tree for all its blocks. A tree made by
  /// `withDepth(d)` verifies up to 2^d transactions; make it with
  /// `withDepth`, as one made by `new` takes fewer than its capacity. Traps
  /// if the tree does not have Bitcoin's rules (`isBitcoin`).
  public func verifierOn(root : Blob, tree : Peaks.Tree) : Chunks.Verifier {
    assert isBitcoin(tree);
    Chunks.onTree(root, tree, true);
  };

  /// The whole tree over `txids`, for `MerkleTree.rightPeaks` (the proofs of
  /// the chunk verifier) and `MerkleTree.branch` (Merkle branches).
  public func merkleTree(txids : [Blob]) : MerkleTree.MerkleTree = MerkleTree.build(txids, #copy, true);
};

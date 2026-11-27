/// Preset: the BAGGED tree. Every node is a single SHA-256 of its two
/// children, and a last node without a partner moves up as it is. The root
/// is then the peaks folded together from right to left, which is called
/// bagging.
///
/// This is the tree shape of RFC 6962 (Certificate Transparency): a tree of
/// n leaves splits at the largest power of two below n. What RFC 6962 adds,
/// and this module does NOT, is a prefix byte in front of every leaf and
/// node, so the hashes here are not those of a transparency log. The plain
/// form is used by AWS Glacier's tree hash and by OpenTimestamps.
///
/// === The root does not commit to the leaf count ===
///
/// Without the prefix bytes a leaf cannot be told from an inner node, and a
/// peak cannot be told from a leaf: the root of `[a, b, c]` is also the root
/// of the two-leaf list `[H(a ++ b), c]`. A verifier must know the number of
/// leaves from elsewhere. `verifyInclusion` takes it as a parameter for that
/// reason.

import Hasher "mo:sha2/Hasher/Sha256";
import Nat "mo:core/Nat";
import Chunks "Chunks";
import Peaks "Peaks";
import MerkleTree "MerkleTree";

module {
  /// An empty bagged tree with room for at least `maxLeaves` leaves: `Peaks`
  /// with single SHA-256 and the `#skip` fill. Leaves are added, and the
  /// root taken, with the functions of `Peaks` (`add`, `addMessage`, `root`).
  public func new(maxLeaves : Nat) : Peaks.Peaks = Peaks.new(maxLeaves, false, #skip);

  /// An empty bagged tree with room for 2^depth leaves (depth at most 61).
  public func withDepth(depth : Nat) : Peaks.Peaks = Peaks.withDepth(depth, false, #skip);

  /// Whether `tree` has the bagged rules: single SHA-256 and the `#skip`
  /// fill.
  public func isBagged(tree : Peaks.Peaks) : Bool = not tree.double and tree.fill == #skip;

  /// The root of a complete list of leaves (at least one), in one shot.
  public func merkleRoot(leaves : [Blob]) : Blob {
    let n = leaves.size();
    assert n >= 1;
    if (n == 1) {
      // The root of a single leaf is the leaf.
      assert leaves[0].size() == 32;
      return leaves[0];
    };
    let tree = new(n);
    ignore tree.addAll(leaves, 0, n, false);
    tree.root();
  };

  /// Verify an INCLUSION PROOF: that `leaf` is the leaf at position `index`
  /// of the tree of `size` leaves with root `root`. `path` holds the siblings
  /// of the leaf's ancestors, lowest first, with the levels left out at which
  /// a node has no sibling (`MerkleTree.branch` of a bagged tree). The algorithm is
  /// that of RFC 9162, section 2.1.3.2, without the prefix bytes. A malformed
  /// proof gives `false`.
  public func verifyInclusion(leaf : Blob, index : Nat, size : Nat, path : [Blob], root : Blob) : Bool {
    // 2^61 - 1 is the largest bound that compares without allocating.
    if (leaf.size() != 32 or index >= size or size > 2305843009213693951) return false;
    var fn = index.toNat64();
    var sn = (size - 1 : Nat).toNat64();
    let node = Hasher.new();
    node.loadBlob32(leaf);
    var j = 0;
    while (j < path.size()) {
      let p = path[j];
      if (p.size() != 32 or sn == 0) return false;
      if ((fn & 1) == 1 or fn == sn) {
        node.combineBlob32State(p, node); // the sibling is on the left
        // A node that moved up without a sibling skips those levels.
        while ((fn & 1) == 0 and fn != 0) {
          fn >>= 1;
          sn >>= 1;
        };
      } else {
        node.combineStateBlob32(node, p); // the sibling is on the right
      };
      fn >>= 1;
      sn >>= 1;
      j += 1;
    };
    sn == 0 and node.equalsBlob32(root);
  };

  /// A chunk verifier for the tree with root `root` and at most 2^maxDepth
  /// leaves. The last chunk is recognised by its empty proof. See `Chunks`,
  /// and the note above: the root does not say how many leaves there are.
  public func verifier(root : Blob, maxDepth : Nat) : Chunks.Verifier = Chunks.new(root, maxDepth, false, #skip, false);

  /// The same verifier on a tree that the caller owns: the
  /// tree is emptied, nothing is allocated but the verifier's record, and a
  /// rejected chunk fails the verifier (see `Chunks.onTree`). A tree made by
  /// `withDepth(d)` verifies up to 2^d leaves. Traps if the tree does not
  /// have the bagged rules (`isBagged`).
  public func verifierOn(root : Blob, tree : Peaks.Peaks) : Chunks.Verifier {
    assert isBagged(tree);
    Chunks.onTree(root, tree, false);
  };

  /// The whole tree over `leaves`, for `MerkleTree.rightPeaks` (the proofs of
  /// the chunk verifier) and `MerkleTree.branch` (inclusion proofs).
  public func merkleTree(leaves : [Blob]) : MerkleTree.MerkleTree = MerkleTree.build(leaves, #skip, false);
};

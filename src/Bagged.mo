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
import Sha256 "mo:sha2/Sha256";
import Nat "mo:core/Nat";
import Chunks "Chunks";
import Peaks "Peaks";
import Prove "Prove";

module {
  /// A bagged tree: `Peaks` with single SHA-256. The `kind` field only keeps
  /// the trees of different presets apart for the type checker; the core
  /// functions are reached through `peaks`.
  public type Tree = { peaks : Peaks.Peaks; kind : { #bagged } };

  /// An empty tree with room for at least `maxLeaves` leaves.
  public func new(maxLeaves : Nat) : Tree = {
    peaks = Peaks.new(maxLeaves, false);
    kind = #bagged;
  };

  /// Add a leaf (32 bytes).
  public func add(self : Tree, leaf : Blob) = self.peaks.add(leaf);

  /// Add the SHA-256 of a message of any length as a leaf, through `digest`
  /// (see `Peaks.addMessage`).
  public func addMessage(self : Tree, digest : Sha256.Digest, message : Blob) = self.peaks.addMessage(digest, message);

  /// The number of leaves added so far.
  public func count(self : Tree) : Nat64 = self.peaks.count;

  /// The root of the leaves added so far (at least one). The tree is left
  /// unchanged.
  public func root(self : Tree) : Blob = self.peaks.root(#skip);

  /// The root of a complete list of leaves (at least one), in one shot.
  public func merkleRoot(leaves : [Blob]) : Blob {
    let n = leaves.size();
    assert n >= 1;
    let peaks = Peaks.new(n, false);
    var i = 0;
    while (i + 1 < n) {
      peaks.addPair(leaves[i], leaves[i + 1]);
      i += 2;
    };
    if (i < n) peaks.add(leaves[i]);
    peaks.root(#skip);
  };

  /// Verify an INCLUSION PROOF: that `leaf` is the leaf at position `index`
  /// of the tree of `size` leaves with root `root`. `path` holds the siblings
  /// of the leaf's ancestors, lowest first, with the levels left out at which
  /// a node has no sibling (`Prove.branch` with `#skip`). The algorithm is
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

  /// The levels of the tree over `leaves`, for `Prove.rightPeaks` (the proofs
  /// of the chunk verifier) and `Prove.branch` (inclusion proofs).
  public func levels(leaves : [Blob]) : [[Blob]] = Prove.levels(leaves, #skip, false);
};

/// CHUNKED verification of a list of leaves against a known Merkle root: the
/// leaves arrive in chunks, in order, and each chunk is checked when it
/// arrives, with no chunk trusted and only a few hashes kept.
///
/// === The check ===
///
/// The verifier keeps the tree over the leaves accepted so far (`Peaks`). A
/// chunk brings the next leaves and a PROOF for the leaves still to come: the
/// peaks to the right of the chunk's last leaf, lowest first
/// (`Prove.rightPeaks`). The verifier then
///
///   1. adds the leaves of the chunk to its tree,
///   2. closes the tree with the proof (`Peaks.close`),
///   3. compares the result with the root,
///   4. and keeps the grown tree if they are equal.
///
/// Every chunk is checked against the root itself, and the proof is used once
/// and not stored. An empty proof says that the chunk is the last one.
///
/// A chunk's leaves are added before the check can fail, so the peaks are
/// copied aside first and copied back if the chunk is rejected. Verification
/// allocates nothing.
///
/// === Cost ===
///
/// One node is hashed per leaf, as for building the tree once, plus one per
/// level for closing the tree, per chunk. With many small chunks the closing
/// dominates.
///
/// === What a Merkle root cannot tell ===
///
/// The check proves "these leaves, in this order, hash to the root". It does
/// not prove that the leaves are leaves: in a tree without domain separation
/// the nodes of any whole level verify just as well as a shorter list. The
/// caller must know from elsewhere what the leaves are, or how many there
/// are. See the notes in the README.

import Hasher "mo:sha2/Hasher/Sha256";
import Nat "mo:core/Nat";
import Peaks "Peaks";

module {
  /// The verifier's state. A static record; it can be declared `stable`.
  public type Verifier = {
    /// The root the leaves must hash to.
    root : Blob;
    /// The tree over the leaves accepted so far; `tree.count` is their number.
    tree : Peaks.Peaks;
    /// Room to copy the peaks aside while a chunk is being checked.
    backup : Peaks.Peaks;
    /// The tree's rule for a node without a right sibling.
    fill : Peaks.Fill;
    /// Whether equal siblings are rejected (see `Bitcoin`).
    checked : Bool;
    /// Whether a chunk has been accepted with an empty proof.
    var done : Bool;
  };

  /// A verifier for the tree with root `root` (32 bytes) and at most
  /// 2^maxDepth leaves, built with single or double SHA-256 and the given
  /// `fill`. With `checked`, a chunk that would combine two equal siblings is
  /// rejected. The presets have a `verifier` function that fills these in.
  public func new(root : Blob, maxDepth : Nat, double : Bool, fill : Peaks.Fill, checked : Bool) : Verifier {
    assert root.size() == 32 and maxDepth <= 61;
    {
      root;
      tree = Peaks.withDepth(maxDepth, double);
      backup = Peaks.withDepth(maxDepth, double);
      fill;
      checked;
      var done = false;
    };
  };

  /// The number of leaves accepted so far.
  public func count(self : Verifier) : Nat64 = self.tree.count;

  /// Whether the upload is complete: the last accepted chunk came with an
  /// empty proof. In a Bitcoin tree with its checks, and in a bagged tree, no
  /// leaf can follow then. In a zero-padded tree an empty proof only says
  /// that all further leaves are zero.
  public func complete(self : Verifier) : Bool = self.done;

  func wellFormed(hashes : [Blob]) : Bool {
    var i = 0;
    while (i < hashes.size()) {
      if (hashes[i].size() != 32) return false;
      i += 1;
    };
    true;
  };

  /// Verify the next chunk of leaves (32 bytes each) with the proof `next`
  /// for the leaves after the chunk, and accept it if it checks out: `true`
  /// and the verifier advances; otherwise `false` and the verifier is
  /// unchanged. An empty `next` claims that the chunk is the last one.
  /// Allocation-free.
  public func verifyChunk(self : Verifier, leaves : [Blob], next : [Blob]) : Bool {
    if (self.done or leaves.size() == 0 or not wellFormed(leaves) or not wellFormed(next)) return false;
    let tree = self.tree;
    // A tree of 2^maxDepth leaves is the most there is room for.
    let maxLeaves = (tree.capacity() + 1) / 2;
    if (leaves.size().toNat64() > maxLeaves - tree.count) return false;
    Peaks.copy(tree, self.backup);
    // 1. Add the chunk.
    var ok = true;
    var j = 0;
    if (self.checked) {
      label adding while (j < leaves.size()) {
        if (not tree.addChecked(leaves[j])) {
          ok := false;
          break adding;
        };
        j += 1;
      };
    } else {
      while (j < leaves.size()) {
        tree.add(leaves[j]);
        j += 1;
      };
    };
    // 2. and 3. Close the tree with the proof and compare with the root.
    if (ok and tree.close(next, self.fill, self.checked) and tree.spare().equalsBlob32(self.root)) {
      // 4. Keep the grown tree.
      self.done := next.size() == 0;
      return true;
    };
    Peaks.copy(self.backup, tree);
    false;
  };
};

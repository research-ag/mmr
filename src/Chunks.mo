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
/// Verification allocates nothing.
///
/// === A rejected chunk ===
///
/// A chunk's leaves are added before the check can fail, so nothing is copied
/// aside and a rejected chunk may leave the tree half-updated. A rejected
/// chunk, of whatever kind (malformed, too long, not matching the root), makes
/// the verifier FAILED (`broken`): it accepts nothing more. A
/// canister that traps on a rejected chunk gets the same by the trap rolling
/// the call back; one that does not must drop the verifier.
///
/// `onTree` also lets the caller own the hashers: one tree, allocated once,
/// can serve one verifier after another. The presets have a `verifierOn`
/// function that fills in their rules.
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
  /// The verifier's state. A static record that can be declared `stable`;
  /// its shape is part of the package's interface.
  public type Verifier = {
    /// The root the leaves must hash to.
    root : Blob;
    /// The tree over the leaves accepted so far; `tree.count` is their number.
    tree : Peaks.Peaks;
    /// The tree's rule for a node without a right sibling.
    fill : Peaks.Fill;
    /// Whether equal siblings are rejected (see `Bitcoin`).
    checked : Bool;
    /// Whether a chunk has been accepted with an empty proof.
    var done : Bool;
    /// Whether a chunk was rejected after its leaves were added. The tree is
    /// then half-updated and the verifier accepts nothing more.
    var failed : Bool;
  };

  /// A verifier for the tree with root `root` (32 bytes) and at most
  /// 2^maxDepth leaves, built with single or double SHA-256 and the given
  /// `fill`. With `checked`, a chunk that would combine two equal siblings is
  /// rejected. The presets have a `verifier` function that fills these in.
  ///
  /// The verifier allocates its tree. A rejected chunk makes it `failed`.
  public func new(root : Blob, maxDepth : Nat, double : Bool, fill : Peaks.Fill, checked : Bool) : Verifier {
    assert maxDepth <= 61;
    onTree(root, Peaks.withDepth(maxDepth, double), fill, checked);
  };

  /// A verifier on a tree that the caller owns. The tree is emptied (its
  /// count set to 0; what its hashers hold does not matter), and its
  /// `double` is the verifier's. A tree made by `Peaks.withDepth(d, ...)`
  /// verifies up to 2^d leaves. Only one verifier may use a tree at a time,
  /// and the caller must not touch it meanwhile.
  public func onTree(root : Blob, tree : Peaks.Peaks, fill : Peaks.Fill, checked : Bool) : Verifier {
    assert root.size() == 32;
    tree.count := 0;
    {
      root;
      tree;
      fill;
      checked;
      var done = false;
      var failed = false;
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

  /// Whether the verifier has failed: a chunk was rejected after its leaves
  /// were added. It accepts nothing more.
  public func broken(self : Verifier) : Bool = self.failed;

  /// Verify the next chunk of leaves (32 bytes each) with the proof `next`
  /// for the leaves after the chunk, and accept it if it checks out: `true`
  /// and the verifier advances; otherwise `false`. An empty `next` claims
  /// that the chunk is the last one. Allocation-free.
  ///
  /// After `false` the verifier has failed, whatever was wrong with the chunk
  /// (a call on a verifier that is done or has failed changes nothing).
  public func verifyChunk(self : Verifier, leaves : [Blob], next : [Blob]) : Bool {
    if (self.done or self.failed) return false;
    let tree = self.tree;
    // A tree of 2^maxDepth leaves is the most there is room for, and its
    // proofs have at most one peak per level. A longer proof is not walked.
    let maxDepth = tree.hasher.size() - 2 : Nat;
    let maxLeaves = (tree.capacity() + 1) / 2;
    if (
      leaves.size() == 0 or next.size() > maxDepth or not wellFormed(leaves) or not wellFormed(next) or leaves.size().toNat64() > maxLeaves - tree.count
    ) {
      self.failed := true;
      return false;
    };
    // 1. Add the chunk, in pairs. 2. and 3. Close the tree with the proof
    // and compare with the root.
    if (
      tree.addAll(leaves, 0, leaves.size(), self.checked) and tree.close(next, self.fill, self.checked) and tree.spare().equalsBlob32(self.root)
    ) {
      // 4. Keep the grown tree.
      self.done := next.size() == 0;
      return true;
    };
    self.failed := true;
    false;
  };
};

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
/// A chunk's leaves are added before the check can fail. What happens to the
/// tree then is the caller's choice:
///
///   - WITH A BACKUP (`new`, and the presets' `verifier`), the peaks are
///     copied aside before every chunk and copied back if it is rejected. The
///     verifier is as it was, and the upload can go on with a correct chunk.
///
///   - WITHOUT ONE (`onTree` with `null`), nothing is copied, and a chunk
///     that fails after its leaves were added leaves the tree half-updated.
///     The verifier is then BROKEN and accepts nothing more. This suits a
///     canister that traps on a rejected chunk: the trap rolls the call back,
///     the tree with it, and a backup would never be read.
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
    /// Room to copy the peaks aside while a chunk is being checked, if a
    /// rejected chunk is to leave the verifier as it was.
    backup : ?Peaks.Peaks;
    /// The tree's rule for a node without a right sibling.
    fill : Peaks.Fill;
    /// Whether equal siblings are rejected (see `Bitcoin`).
    checked : Bool;
    /// Whether a chunk has been accepted with an empty proof.
    var done : Bool;
    /// Whether a chunk was rejected with no backup to restore the tree from.
    var failed : Bool;
  };

  /// A verifier for the tree with root `root` (32 bytes) and at most
  /// 2^maxDepth leaves, built with single or double SHA-256 and the given
  /// `fill`. With `checked`, a chunk that would combine two equal siblings is
  /// rejected. The presets have a `verifier` function that fills these in.
  ///
  /// The verifier allocates its tree and a backup, so that a rejected chunk
  /// leaves it unchanged.
  public func new(root : Blob, maxDepth : Nat, double : Bool, fill : Peaks.Fill, checked : Bool) : Verifier {
    assert maxDepth <= 61;
    onTree(root, Peaks.withDepth(maxDepth, double), ?Peaks.withDepth(maxDepth, double), fill, checked);
  };

  /// A verifier on a tree that the caller owns. The tree is emptied (its
  /// count set to 0; what its hashers hold does not matter), and its
  /// `double` is the verifier's. A tree made by `Peaks.withDepth(d, ...)`
  /// verifies up to 2^d leaves. Only one verifier may use a tree at a time,
  /// and the caller must not touch it meanwhile.
  ///
  /// `backup` is a second tree of at least the same size, or `null`. With
  /// `null`, a chunk that is rejected after its leaves were added breaks the
  /// verifier: it accepts nothing more, and the caller must trap or drop it.
  public func onTree(root : Blob, tree : Peaks.Peaks, backup : ?Peaks.Peaks, fill : Peaks.Fill, checked : Bool) : Verifier {
    assert root.size() == 32;
    switch backup {
      case (?b) assert b.hasher.size() >= tree.hasher.size();
      case null {};
    };
    tree.count := 0;
    {
      root;
      tree;
      backup;
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

  /// Whether the verifier is broken: a chunk was rejected and there was no
  /// backup to restore the tree from (see `onTree`).
  public func broken(self : Verifier) : Bool = self.failed;

  /// Verify the next chunk of leaves (32 bytes each) with the proof `next`
  /// for the leaves after the chunk, and accept it if it checks out: `true`
  /// and the verifier advances; otherwise `false`. An empty `next` claims
  /// that the chunk is the last one. Allocation-free.
  ///
  /// After `false` a verifier with a backup is unchanged. One without is
  /// unchanged if the chunk was malformed or too long, and broken otherwise.
  public func verifyChunk(self : Verifier, leaves : [Blob], next : [Blob]) : Bool {
    if (self.done or self.failed or leaves.size() == 0) return false;
    let tree = self.tree;
    // A tree of 2^maxDepth leaves is the most there is room for, and its
    // proofs have at most one peak per level. A longer proof is not walked.
    let maxDepth = tree.hasher.size() - 2 : Nat;
    if (next.size() > maxDepth or not wellFormed(leaves) or not wellFormed(next)) return false;
    let maxLeaves = (tree.capacity() + 1) / 2;
    if (leaves.size().toNat64() > maxLeaves - tree.count) return false;
    switch (self.backup) {
      case (?backup) Peaks.copy(tree, backup);
      case null {};
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
    switch (self.backup) {
      case (?backup) Peaks.copy(backup, tree);
      case null self.failed := true;
    };
    false;
  };
};

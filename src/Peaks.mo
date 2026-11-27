/// The core of the package: a Merkle mountain range as an array of peaks with
/// a counter, and the few operations that every Merkle tree built from it
/// shares. The presets (`Bitcoin`, `Bagged`, `ZeroPadded`) and the chunk verifier
/// (`Chunks`) are thin layers over this module; use it directly to build a
/// tree format of your own.
///
/// Everything here hashes with SHA-256 and combines two 32-byte hashes as one
/// 64-byte message, `H(left ++ right)`, with no prefix. A tree is either
/// SINGLE (one SHA-256 per node) or DOUBLE (SHA-256 twice, as in Bitcoin),
/// and has a `Fill`, the rule for a node without a right sibling. These two
/// rules are what tells the tree formats apart, and a tree keeps both in its
/// record: the presets are only constructors that choose them. Nothing in this module allocates, except where a `Blob` or an array is
/// returned.
///
/// === The structure ===
///
/// The leaves added so far are covered by perfect subtrees, the PEAKS: one of
/// 2^k leaves for every 1-bit k of the leaf count, largest on the left. Slot k
/// of the pool holds the root of the peak of height k, if the count has that
/// bit; the last slot is a SPARE, where the node that is being worked on
/// lives. So `count` alone says which slots are occupied.
///
/// === The operations ===
///
///   - `carry` inserts the node in the spare as a new peak of a given height
///     and merges upward while the count has a 1-bit: the increment of a
///     binary counter. Adding a leaf is a carry at height 0 (`add`), adding
///     two leaves fused straight from their Blobs a carry at height 1
///     (`addPair`), adding the root of a subtree a carry at its height.
///     `addAll` adds a run of leaves, in pairs where it can.
///
///   - `close` computes a root from the peaks without changing them. It walks
///     up from the lowest peak: where the count has a 1-bit it combines with
///     the peak on the LEFT; elsewhere something has to stand on the RIGHT,
///     and what that is is the tree's `Fill`. With a list
///     of peaks for the right-hand side, the same walk verifies a prefix of a
///     tree against its root.
///
///   - `foldBranch` folds one node up a list of siblings: the verification of
///     an inclusion proof.
///
///   - `copy`, `toBlobs` and `load` save, export and restore the peaks.

import Hasher "mo:sha2/Hasher/Sha256";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";

module {
  /// The peaks of a tree. Slot k of `hasher` holds the peak of height k
  /// exactly when bit k of `count` is set; the last slot is the spare.
  /// `double` selects double SHA-256 per node, and `fill` the rule for a
  /// node without a right sibling when a root is computed. A static record
  /// that can be declared `stable`; its shape is part of the package's
  /// interface.
  public type Peaks = {
    hasher : [var Hasher.Hasher];
    double : Bool;
    fill : Fill;
    var count : Nat64;
  };

  /// What stands on the right of a node that has no right sibling, when a
  /// root is computed:
  ///
  ///   - `#skip`: nothing. The node moves up as it is, and the peaks are
  ///     simply folded together from right to left ("bagging"). This is the
  ///     tree shape of RFC 6962, of AWS Glacier's tree hash and of
  ///     OpenTimestamps.
  ///   - `#copy`: the node itself. Bitcoin's rule for an odd last node.
  ///   - `#zeros`: the root of an all-zero subtree of the same height, taken
  ///     from `table` (see `zeros`). With `depth = ?d` the tree is padded to
  ///     exactly 2^d leaves, and `table` needs d + 1 entries; with `null` to
  ///     the smallest power of two that holds the leaves. SSZ and BitTorrent
  ///     v2 work this way.
  public type Fill = {
    #skip;
    #copy;
    #zeros : { table : [Blob]; depth : ?Nat };
  };

  /// An empty tree with room for at least `maxLeaves` leaves. Allocates
  /// `floor(log2 maxLeaves) + 2` hashers: one slot per bit of the count, and
  /// the spare.
  public func new(maxLeaves : Nat, double : Bool, fill : Fill) : Peaks {
    assert maxLeaves >= 1;
    // floor(log2 maxLeaves), from the leading zeros. Not by doubling a `Nat`:
    // its multiplication allocates once the product passes 2^31.
    withDepth((63 - Nat64.bitcountLeadingZero(maxLeaves.toNat64())).toNat(), double, fill);
  };

  /// An empty tree with room for 2^depth leaves (depth at most 61): slots 0
  /// to depth, and the spare.
  public func withDepth(depth : Nat, double : Bool, fill : Fill) : Peaks {
    assert depth <= 61;
    {
      hasher = VarArray.tabulate<Hasher.Hasher>(depth + 2, func(_) { Hasher.new() });
      double;
      fill;
      var count = 0;
    };
  };

  /// The largest number of leaves the tree can hold: one less than a power of
  /// two, since every slot can be occupied at once.
  public func capacity(self : Peaks) : Nat64 = (1 << (self.hasher.size() - 1 : Nat).toNat64()) - 1;

  /// The spare hasher. The adapters below put a node here before `carry`, and
  /// `close` leaves its result here.
  public func spare(self : Peaks) : Hasher.Hasher = self.hasher[self.hasher.size() - 1];

  // ---------------------------------------------------------------------------
  // Adding
  // ---------------------------------------------------------------------------

  /// Insert the node in the spare as a peak of height `height`, merging upward
  /// while the count has a 1-bit: `count` grows by 2^height. The low `height`
  /// bits of the count must be zero, so that the node is aligned. Traps if the
  /// capacity is exceeded.
  public func carry(self : Peaks, height : Nat64) {
    let hasher = self.hasher;
    let top = hasher.size() - 1 : Nat;
    let node = hasher[top];
    let count = self.count;
    let double = self.double;
    assert (count & ((1 << height) - 1)) == 0;
    var k = height;
    while (((count >> k) & 1) == 1) {
      node.combineState(hasher[k.toNat()], node); // H(peak ++ node)
      if (double) node.hashState(node);
      k += 1;
    };
    // The node rests in slot k, and the hasher that was there is the spare.
    let kk = k.toNat();
    if (kk >= top) Runtime.trap("mmr: capacity exceeded");
    hasher[top] := hasher[kk];
    hasher[kk] := node;
    self.count := count + (1 << height);
  };

  /// `carry` with a check for EQUAL SIBLINGS: returns `false`, and leaves the
  /// tree as it was, if the node would be merged with a peak that hashes
  /// alike. A valid Bitcoin block never has such a pair (see `Bitcoin`).
  public func carryChecked(self : Peaks, height : Nat64) : Bool {
    let hasher = self.hasher;
    let top = hasher.size() - 1 : Nat;
    let node = hasher[top];
    let count = self.count;
    let double = self.double;
    assert (count & ((1 << height) - 1)) == 0;
    var k = height;
    while (((count >> k) & 1) == 1) {
      let peak = hasher[k.toNat()];
      if (peak.equalsState(node)) return false;
      node.combineState(peak, node);
      if (double) node.hashState(node);
      k += 1;
    };
    let kk = k.toNat();
    if (kk >= top) Runtime.trap("mmr: capacity exceeded");
    hasher[top] := hasher[kk];
    hasher[kk] := node;
    self.count := count + (1 << height);
    true;
  };

  /// Add a leaf, a 32-byte `Blob`. Traps if it is not 32 bytes long.
  public func add(self : Peaks, leaf : Blob) {
    spare(self).loadBlob32(leaf);
    carry(self, 0);
  };

  /// `add` with the check for equal siblings (see `carryChecked`).
  public func addChecked(self : Peaks, leaf : Blob) : Bool {
    spare(self).loadBlob32(leaf);
    carryChecked(self, 0);
  };

  /// Add two leaves at once. They are fused straight from their Blobs, which
  /// is cheaper than adding them one by one. The count must be even.
  public func addPair(self : Peaks, left : Blob, right : Blob) {
    let node = spare(self);
    node.combineBlob32(left, right);
    if (self.double) node.hashState(node);
    carry(self, 1);
  };

  /// `addPair` with the check for equal siblings, the two leaves included.
  public func addPairChecked(self : Peaks, left : Blob, right : Blob) : Bool {
    if (left == right) return false;
    let node = spare(self);
    node.combineBlob32(left, right);
    if (self.double) node.hashState(node);
    carryChecked(self, 1);
  };

  /// Add the leaves `leaves[from]` to `leaves[to - 1]`, in pairs wherever the
  /// count allows: a first leaf alone if the count is odd, so that the pairs
  /// are aligned, then pairs, then a last leaf alone if one is left. The
  /// result is that of adding them one by one, at about two thirds of the
  /// loading cost.
  ///
  /// With `checked`, returns `false` as soon as two equal siblings would be
  /// combined; the leaves before them stay added. Otherwise `true`.
  public func addAll(self : Peaks, leaves : [Blob], from : Nat, to : Nat, checked : Bool) : Bool {
    assert from <= to and to <= leaves.size();
    var i = from;
    if (checked) {
      if (i < to and (self.count & 1) == 1) {
        if (not addChecked(self, leaves[i])) return false;
        i += 1;
      };
      while (i + 1 < to) {
        if (not addPairChecked(self, leaves[i], leaves[i + 1])) return false;
        i += 2;
      };
      if (i < to) return addChecked(self, leaves[i]);
    } else {
      if (i < to and (self.count & 1) == 1) {
        add(self, leaves[i]);
        i += 1;
      };
      while (i + 1 < to) {
        addPair(self, leaves[i], leaves[i + 1]);
        i += 2;
      };
      if (i < to) add(self, leaves[i]);
    };
    true;
  };

  /// Add a leaf that is held in a `Hasher`. The hasher is only read.
  public func addState(self : Peaks, leaf : Hasher.Hasher) {
    spare(self).loadState(leaf);
    carry(self, 0);
  };

  /// Add the hash of a message of any length as a leaf: SHA-256 of the
  /// message in a single tree, SHA-256 twice in a double one. `digest` is a
  /// SHA-256 `Digest` to work in; it is reset first, so one can serve all
  /// leaves. No `Blob` is made of the hash.
  public func addMessage(self : Peaks, digest : Sha256.Digest, message : Blob) {
    digest.reset();
    digest.writeBlob(message);
    digest.close();
    let node = spare(self);
    if (self.double) node.hashState(digest.state) else node.loadState(digest.state);
    carry(self, 0);
  };

  // ---------------------------------------------------------------------------
  // Closing
  // ---------------------------------------------------------------------------

  /// Compute a root from the peaks, into the spare (`spare`), without
  /// changing the peaks.
  ///
  /// Starting from the lowest peak and going up one height at a time, the
  /// node in hand is combined with
  ///
  ///   - the peak of the tree on its LEFT, where the count has a 1-bit,
  ///   - else the next entry of `proof` on its RIGHT,
  ///   - else what the tree's `fill` says.
  ///
  /// With an empty `proof` this is the root of the tree. With the peaks to
  /// the right of the tree's last leaf as `proof`, lowest first, it is the
  /// root of the larger tree that those peaks complete: the check of a prefix
  /// against a known root.
  ///
  /// With `checked`, returns `false` if two equal siblings would be combined.
  /// Also `false` if the walk goes beyond height 62. Otherwise `true`.
  ///
  /// Traps on a tree padded to a fixed depth d that holds more than 2^d
  /// leaves: it has no root of that depth. Adding does not check this, so
  /// that adding costs the same in every format; the trap comes here.
  public func close(self : Peaks, proof : [Blob], checked : Bool) : Bool {
    let hasher = self.hasher;
    let fill = self.fill;
    let acc = hasher[hasher.size() - 1];
    let count = self.count;
    let double = self.double;
    let fixedDepth : Nat64 = switch fill {
      case (#zeros({ depth = ?d })) {
        let depth = d.toNat64();
        if (count > (1 << depth)) Runtime.trap("mmr: more leaves than the 2^depth places of a zero-padded tree");
        depth;
      };
      case _ 0;
    };
    if (count == 0) {
      // Only a tree padded to a fixed depth has a root without leaves.
      switch fill {
        case (#zeros({ table; depth = ?d })) {
          acc.loadBlob32(table[d]);
          return proof.size() == 0;
        };
        case _ Runtime.trap("mmr: an empty tree has no root");
      };
    };
    // The lowest peak is a left child. Copy it, so that the peaks stay as
    // they are; `rest` is the count without that peak.
    var k = Nat64.bitcountTrailingZero(count);
    acc.loadState(hasher[k.toNat()]);
    let rest = count & (count - 1);
    var i = 0; // the next entry of the proof
    while ((rest >> k) > 0 or i < proof.size() or k < fixedDepth) {
      if (k >= 62) return false;
      if (((rest >> k) & 1) == 1) {
        let peak = hasher[k.toNat()];
        if (checked and peak.equalsState(acc)) return false;
        acc.combineState(peak, acc); // H(peak ++ acc)
        if (double) acc.hashState(acc);
      } else if (i < proof.size()) {
        if (checked and acc.equalsBlob32(proof[i])) return false;
        acc.combineStateBlob32(acc, proof[i]); // H(acc ++ peak of the proof)
        if (double) acc.hashState(acc);
        i += 1;
      } else {
        switch fill {
          case (#skip) {};
          case (#copy) {
            acc.combineState(acc, acc); // H(acc ++ acc)
            if (double) acc.hashState(acc);
          };
          case (#zeros({ table })) {
            acc.combineStateBlob32(acc, table[k.toNat()]); // H(acc ++ Z_k)
            if (double) acc.hashState(acc);
          };
        };
      };
      k += 1;
    };
    true;
  };

  /// The root of the tree, as a `Blob`. The tree is left unchanged: keep
  /// adding leaves and take the root again.
  public func root(self : Peaks) : Blob {
    ignore close(self, [], false);
    spare(self).readSum();
  };

  // ---------------------------------------------------------------------------
  // Branches
  // ---------------------------------------------------------------------------

  /// Fold `node` up a list of siblings, lowest first: where bit j of `index`
  /// is set the j-th sibling is on the left, `H(sibling ++ node)`, otherwise
  /// on the right, `H(node ++ sibling)`. This turns a leaf and its inclusion
  /// proof into the root, for trees in which every level of the path has a
  /// sibling (Bitcoin with the duplicates written out, zero-padded trees).
  /// Traps if a sibling is not 32 bytes long.
  public func foldBranch(node : Hasher.Hasher, index : Nat64, siblings : [Blob], double : Bool) {
    var j = 0;
    var bits = index;
    while (j < siblings.size()) {
      if ((bits & 1) == 1) {
        node.combineBlob32State(siblings[j], node);
      } else {
        node.combineStateBlob32(node, siblings[j]);
      };
      if (double) node.hashState(node);
      bits >>= 1;
      j += 1;
    };
  };

  // ---------------------------------------------------------------------------
  // Saving and restoring
  // ---------------------------------------------------------------------------

  /// Copy the count and the peaks of `from` into `to`, which must have at
  /// least as many slots. Used to undo: copy aside, try, copy back.
  public func copy(from : Peaks, to : Peaks) {
    assert to.hasher.size() >= from.hasher.size();
    var bits = from.count;
    while (bits != 0) {
      let k = Nat64.bitcountTrailingZero(bits).toNat();
      to.hasher[k].loadState(from.hasher[k]);
      bits &= bits - 1; // on to the next peak
    };
    to.count := from.count;
  };

  /// The peaks as Blobs, lowest first. Together with the count they are the
  /// whole state of the tree.
  public func toBlobs(self : Peaks) : [Blob] {
    var bits = self.count;
    Array.tabulate<Blob>(
      Nat64.bitcountNonZero(bits).toNat(),
      func(_) {
        let k = Nat64.bitcountTrailingZero(bits).toNat();
        bits &= bits - 1;
        self.hasher[k].readSum();
      },
    );
  };

  /// Set the tree to `count` leaves with the given peaks, lowest first, as
  /// `toBlobs` returns them. Returns `false`, and leaves the tree as it was,
  /// if the count is beyond the capacity, or if the peaks are not one 32-byte
  /// `Blob` per 1-bit of the count.
  public func load(self : Peaks, count : Nat64, peaks : [Blob]) : Bool {
    if (count > capacity(self) or Nat64.bitcountNonZero(count).toNat() != peaks.size()) return false;
    var i = 0;
    while (i < peaks.size()) {
      if (peaks[i].size() != 32) return false;
      i += 1;
    };
    var bits = count;
    i := 0;
    while (bits != 0) {
      let k = Nat64.bitcountTrailingZero(bits).toNat();
      self.hasher[k].loadBlob32(peaks[i]);
      bits &= bits - 1;
      i += 1;
    };
    self.count := count;
    true;
  };

  // ---------------------------------------------------------------------------
  // Zero subtrees
  // ---------------------------------------------------------------------------

  /// The roots of the all-zero subtrees of heights 0 to `depth`: `Z_0` is 32
  /// zero bytes, and `Z_(k+1) = H(Z_k ++ Z_k)`. The table for `#zeros`.
  public func zeros(depth : Nat, double : Bool) : [Blob] {
    let h = Hasher.new();
    var z : Blob = "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00";
    Array.tabulate<Blob>(
      depth + 1,
      func(k) {
        if (k > 0) {
          h.combineBlob32(z, z);
          if (double) h.hashState(h);
          z := h.readSum();
        };
        z;
      },
    );
  };
};

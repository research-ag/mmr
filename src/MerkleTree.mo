/// The whole tree, every level of it: what the PROVER needs. This is the
/// side that has all the leaves, typically off-chain or in a test; the
/// verifying side (`Peaks.close`, `Peaks.foldBranch`, `Chunks`) keeps only
/// the peaks.
///
/// The LEVELS of a tree: level 0 is the leaves, and each next level the
/// hashes of pairs of the one below. A last node without a partner is
/// treated as the tree's `Fill` says: moved up as it is (`#skip`), paired
/// with itself (`#copy`), or paired with the all-zero subtree of its height
/// (`#zeros`). The levels hold only nodes that cover real leaves, so they
/// take about twice the memory of the leaves.
///
/// A `MerkleTree` keeps its levels together with the rules they were built
/// with, so that the proofs taken from it are always those of its format.
/// The presets have a `merkleTree` function that fills the rules in.

import Hasher "mo:sha2/Hasher/Sha256";
import Array "mo:core/Array";
import List "mo:core/List";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import Peaks "Peaks";

module {
  /// The levels of a tree, leaves first and the root alone last, with the
  /// rules they were built with.
  public type MerkleTree = {
    levels : [[Blob]];
    fill : Peaks.Fill;
    double : Bool;
  };

  /// The tree over `leaves` (at least one, each 32 bytes), built with the
  /// given `fill` and single or double SHA-256. Traps if a leaf is not 32
  /// bytes long, or if the fill pads to a fixed depth d and there are more
  /// than 2^d leaves.
  public func build(leaves : [Blob], fill : Peaks.Fill, double : Bool) : MerkleTree {
    assert leaves.size() >= 1;
    // A leaf that is never combined (a single one, or the last of a level
    // that moves up as it is) would otherwise go unchecked.
    for (leaf in leaves.values()) assert leaf.size() == 32;
    let h = Hasher.new();
    func node(left : Blob, right : Blob) : Blob {
      h.combineBlob32(left, right);
      if (double) h.hashState(h);
      h.readSum();
    };
    let fixedDepth = switch fill {
      case (#zeros({ depth })) {
        if (leaves.size() > 2 ** depth) Runtime.trap("merkle: more leaves than the 2^depth places of a zero-padded tree");
        depth;
      };
      case _ 0;
    };
    let all = List.singleton<[Blob]>(leaves);
    var level = leaves;
    var k = 0;
    while (level.size() > 1 or k < fixedDepth) {
      let below = level;
      let len = below.size();
      level := Array.tabulate<Blob>(
        (len + 1) / 2,
        func(i) {
          let left = below[2 * i];
          if (2 * i + 1 < len) node(left, below[2 * i + 1]) else switch fill {
            case (#skip) left;
            case (#copy) node(left, left);
            case (#zeros({ table })) node(left, table[k]);
          };
        },
      );
      all.add(level);
      k += 1;
    };
    { levels = all.toArray(); fill; double };
  };

  /// The number of leaves.
  public func size(self : MerkleTree) : Nat = self.levels[0].size();

  /// The root.
  public func root(self : MerkleTree) : Blob = self.levels[self.levels.size() - 1][0];

  /// The proof for the first `m` leaves (0 <= m <= n): the PEAKS TO THE RIGHT
  /// of leaf m - 1, lowest first. These are the right siblings of that leaf's
  /// ancestors, as far as they cover real leaves; empty for m = n. This is
  /// what `Peaks.close` and `Chunks.verifyChunk` take as `proof`, for m >= 1:
  /// they work on a tree that holds at least one leaf. For m = 0 it is the
  /// root alone, the whole tree to the right of nothing.
  public func rightPeaks(self : MerkleTree, m : Nat) : [Blob] {
    let levels = self.levels;
    assert m <= levels[0].size();
    if (m == 0) return [root(self)];
    let out = List.empty<Blob>();
    var k = 0;
    while (k < levels.size()) {
      let idx = (m - 1 : Nat) / (2 ** k);
      if (idx % 2 == 0 and idx + 1 < levels[k].size()) out.add(levels[k][idx + 1]);
      k += 1;
    };
    out.toArray();
  };

  /// The inclusion proof of the leaf at `index`: the siblings of its
  /// ancestors, lowest first. Where a node has no sibling, `#copy` writes the
  /// node itself and `#zeros` the zero subtree, so that those branches have
  /// one entry per level and suit `Peaks.foldBranch`; `#skip` leaves the
  /// level out, as RFC 6962 does (see `Bagged.verifyInclusion`).
  public func branch(self : MerkleTree, index : Nat) : [Blob] {
    let levels = self.levels;
    assert index < levels[0].size();
    let out = List.empty<Blob>();
    var k = 0;
    while (k + 1 < levels.size()) {
      let idx = index / (2 ** k);
      let sibling = if (idx % 2 == 0) idx + 1 else (idx - 1 : Nat);
      if (sibling < levels[k].size()) out.add(levels[k][sibling]) else switch (self.fill) {
        case (#skip) {};
        case (#copy) out.add(levels[k][idx]);
        case (#zeros({ table })) out.add(table[k]);
      };
      k += 1;
    };
    out.toArray();
  };
};

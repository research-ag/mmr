/// The PROVER: proofs computed from all the leaves of a tree. This is the
/// side that has the whole list, typically off-chain or in a test; the
/// verifying side (`Peaks.close`, `Peaks.foldBranch`, `Chunks`) needs only the
/// peaks.
///
/// The functions work on the LEVELS of a tree: level 0 is the leaves, and
/// each next level the hashes of pairs of the one below. A last node without
/// a partner is treated as the tree's `Fill` says: moved up as it is
/// (`#skip`), paired with itself (`#copy`), or paired with the all-zero
/// subtree of its height (`#zeros`). The levels hold only nodes that cover
/// real leaves, so they take about twice the memory of the leaves.

import Hasher "mo:sha2/Hasher/Sha256";
import Array "mo:core/Array";
import List "mo:core/List";
import Nat "mo:core/Nat";
import Peaks "Peaks";

module {
  /// The levels of the tree over `leaves` (at least one, each 32 bytes),
  /// built with the given `fill` and single or double SHA-256. The last level
  /// is the root alone.
  public func levels(leaves : [Blob], fill : Peaks.Fill, double : Bool) : [[Blob]] {
    assert leaves.size() >= 1;
    let h = Hasher.new();
    func node(left : Blob, right : Blob) : Blob {
      h.combineBlob32(left, right);
      if (double) h.hashState(h);
      h.readSum();
    };
    let fixedDepth = switch fill {
      case (#zeros({ depth = ?d })) d;
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
    all.toArray();
  };

  /// The root, from the levels.
  public func root(levels : [[Blob]]) : Blob = levels[levels.size() - 1][0];

  /// The proof for the first `m` leaves (0 <= m <= n): the PEAKS TO THE RIGHT
  /// of leaf m - 1, lowest first. These are the right siblings of that leaf's
  /// ancestors, as far as they cover real leaves. The root alone for m = 0,
  /// empty for m = n. This is what `Peaks.close` and `Chunks.verifyChunk`
  /// take as `proof`.
  public func rightPeaks(levels : [[Blob]], m : Nat) : [Blob] {
    assert m <= levels[0].size();
    if (m == 0) return [root(levels)];
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
  /// level out, as RFC 6962 does (see `Bagged.verifyInclusion`). `fill` must
  /// be the one the levels were built with.
  public func branch(levels : [[Blob]], index : Nat, fill : Peaks.Fill) : [Blob] {
    assert index < levels[0].size();
    let out = List.empty<Blob>();
    var k = 0;
    while (k + 1 < levels.size()) {
      let idx = index / (2 ** k);
      let sibling = if (idx % 2 == 0) idx + 1 else (idx - 1 : Nat);
      if (sibling < levels[k].size()) out.add(levels[k][sibling]) else switch fill {
        case (#skip) {};
        case (#copy) out.add(levels[k][idx]);
        case (#zeros({ table })) out.add(table[k]);
      };
      k += 1;
    };
    out.toArray();
  };
};

/// Preset: the ZERO-PADDED tree. Every node is a single SHA-256 of its two
/// children, and the tree has a fixed number of leaf places, a power of two:
/// the places that are not used count as 32 zero bytes. This is the
/// Merkleization of SSZ, the serialization of Ethereum's consensus layer,
/// where the leaves are called chunks; the incremental tree of Ethereum's
/// deposit contract and the file trees of BitTorrent v2 are built the same
/// way.
///
/// The unused places are never hashed. An all-zero subtree has a root that
/// depends only on its height, so those roots are a small table of constants
/// (`Peaks.zeros`), and a node without a right sibling is combined with the
/// constant of its height.
///
/// === The length ===
///
/// A real leaf of 32 zero bytes at the end cannot be told from padding: the
/// lists `[a, b, c]` and `[a, b, c, 0]` have the same root. Where the length
/// can vary, SSZ therefore hashes it in at the end, `H(root ++ length)`
/// (`mixInLength`, `rootWithLength`). A tree of fixed size needs no such
/// step.

import Hasher "mo:sha2/Hasher/Sha256";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Chunks "Chunks";
import Peaks "Peaks";
import Prove "Prove";

module {
  /// A tree with room for 2^depth chunks: the peaks, and the rule for
  /// padding, which holds the table of all-zero subtree roots for heights 0
  /// to depth.
  public type Tree = {
    peaks : Peaks.Peaks;
    fill : Peaks.Fill;
    depth : Nat;
  };

  /// The `Fill` of a tree of 2^depth places.
  public func fillOf(depth : Nat) : Peaks.Fill = #zeros({ table = Peaks.zeros(depth, false); depth = ?depth });

  /// An empty tree with 2^depth leaf places (depth at most 61). The deposit
  /// contract uses depth 32.
  public func new(depth : Nat) : Tree = {
    peaks = Peaks.withDepth(depth, false);
    fill = fillOf(depth);
    depth;
  };

  /// Add a chunk (32 bytes).
  public func add(self : Tree, chunk : Blob) = self.peaks.add(chunk);

  /// The number of chunks added so far.
  public func count(self : Tree) : Nat64 = self.peaks.count;

  /// The root of the tree, padded with zero chunks to its 2^depth places.
  /// Defined for an empty tree as well. The tree is left unchanged.
  public func root(self : Tree) : Blob = self.peaks.root(self.fill);

  /// `H(root ++ length)`, with the length as a 32-byte little-endian number:
  /// SSZ's `mix_in_length`. Traps for a length of 2^64 or more.
  public func mixInLength(root : Blob, length : Nat) : Blob {
    assert root.size() == 32;
    var rest = length.toNat64();
    // The length chunk is written straight into a hasher, so that no array
    // and no Blob is made for it. A `Hasher` holds its 32 bytes as 16
    // half-words, each two bytes with the first one high; the length takes
    // the first eight bytes, lowest first, and the rest stay zero.
    let h = Hasher.new();
    var k = 0;
    while (k < 4) {
      h[k] := (((rest & 0xff) << 8) | ((rest >> 8) & 0xff)).toNat().toNat16();
      rest >>= 16;
      k += 1;
    };
    h.combineBlob32State(root, h);
    h.readSum();
  };

  /// The root with the number of chunks mixed in: the `hash_tree_root` of an
  /// SSZ list of 32-byte elements with a limit of 2^depth, and the root of
  /// the deposit contract.
  public func rootWithLength(self : Tree) : Blob = mixInLength(root(self), self.peaks.count.toNat());

  /// The root of a complete list of chunks, padded with zero chunks to
  /// `limit` places, or to the next power of two if `limit` is `null`: SSZ's
  /// `merkleize`. A `limit` that is not a power of two is rounded up. The
  /// length is not mixed in.
  public func merkleize(chunks : [Blob], limit : ?Nat) : Blob {
    let places = switch limit {
      case (?l) { assert l >= chunks.size(); l };
      case null chunks.size();
    };
    // ceil(log2 places), from the leading zeros of places - 1, computed in
    // `Nat64`. `Nat` arithmetic (a power, a doubling loop, even the
    // subtraction) allocates for a large limit.
    let depth = if (places <= 1) 0 else (64 - Nat64.bitcountLeadingZero(places.toNat64() - 1)).toNat();
    let tree = new(depth);
    ignore tree.peaks.addAll(chunks, 0, chunks.size(), false);
    root(tree);
  };

  /// Verify a MERKLE BRANCH: that `leaf` is the chunk at position `index` of
  /// a tree with root `root`. `branch` holds one sibling per level, lowest
  /// first, so its length is the depth: SSZ's `is_valid_merkle_branch`. A
  /// malformed branch gives `false`.
  public func verifyBranch(leaf : Blob, index : Nat, branch : [Blob], root : Blob) : Bool {
    if (leaf.size() != 32 or branch.size() > 62) return false;
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
    node.loadBlob32(leaf);
    Peaks.foldBranch(node, position, branch, false);
    node.equalsBlob32(root);
  };

  /// A chunk verifier for the tree of 2^depth places with root `root` (the
  /// root without the length mixed in). See `Chunks`. An empty proof says
  /// only that every further chunk is zero; the number of chunks must be
  /// known from elsewhere.
  public func verifier(root : Blob, depth : Nat) : Chunks.Verifier = Chunks.new(root, depth, false, fillOf(depth), false);

  /// The levels of the tree of 2^depth places over `chunks` (at least one),
  /// for `Prove.rightPeaks` (the proofs of the chunk verifier) and
  /// `Prove.branch` (Merkle branches; pass the same fill, `fillOf(depth)`).
  public func levels(chunks : [Blob], depth : Nat) : [[Blob]] = Prove.levels(chunks, fillOf(depth), false);
};

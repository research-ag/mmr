// @testmode wasi
// The chunk verifier on a caller's tree: one tree per format serves every
// verifier, one after another, whatever the one before left in it.
//
// Honest chunks are accepted. A chunk that is refused before anything is
// added (empty, malformed, too long a proof, too many leaves) fails the
// verifier but leaves the tree untouched. One that fails after adding fails
// it for good.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import ZeroPadded "../../src/ZeroPadded";
import Chunks "../../src/Chunks";
import MerkleTree "../../src/MerkleTree";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaf; leaves; slice; flipFirst } = Fixtures;

let depth = 9;
// The trees of the caller, one per format, each with its format's rules.
let trees = [Bitcoin.withDepth(depth), Bagged.withDepth(depth), ZeroPadded.new(depth)];
// Each preset recognises its own trees, which is what its `verifierOn`
// checks.
assert Bitcoin.isBitcoin(trees[0]) and not Bitcoin.isBitcoin(trees[1]) and not Bitcoin.isBitcoin(trees[2]);
assert Bagged.isBagged(trees[1]) and not Bagged.isBagged(trees[0]) and not Bagged.isBagged(trees[2]);
assert ZeroPadded.depthOf(trees[2]) == ?depth and ZeroPadded.depthOf(trees[0]) == null and ZeroPadded.depthOf(trees[1]) == null;

// The rules of different formats differ, and so do two zero-padded depths.
assert not Peaks.sameRules(trees[0], trees[1]) and not Peaks.sameRules(trees[1], trees[2]);
assert not Peaks.sameRules(ZeroPadded.new(3), ZeroPadded.new(4)) and Peaks.sameRules(ZeroPadded.new(4), ZeroPadded.new(4));

// The capacity is what the slots hold, or for a zero-padded tree no more
// than its places.
assert Bitcoin.withDepth(depth).capacity().toNat() + 1 == 2 ** (depth + 1);
assert ZeroPadded.new(depth).capacity().toNat() == 2 ** depth;
assert Peaks.withDepth(10, false, ZeroPadded.fillOf(5)).capacity() == 32;
assert Peaks.withDepth(3, false, ZeroPadded.fillOf(5)).capacity() == 15;

// A zero-padded tree whose slots reach deeper than its padding: a chunk
// beyond its places is rejected, not trapped on.
do {
  let wide = Peaks.withDepth(10, false, ZeroPadded.fillOf(5));
  let ls = leaves(33);
  let v = ZeroPadded.verifierOn(Reference.padded(slice(ls, 0, 32), 5), wide);
  assert not v.verifyChunk(ls, []) and v.broken() and wide.count == 0;
  let w = ZeroPadded.verifierOn(Reference.padded(slice(ls, 0, 32), 5), wide);
  assert w.verifyChunk(slice(ls, 0, 32), []) and w.complete();
};

let sizes : [Nat] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 23, 31, 32, 33, 64, 100, 257];

// `Chunks.onTree` directly, with the check for equal siblings in Bitcoin.
for (n in sizes.values()) {
  let ls = leaves(n);
  let kinds : [(Peaks.Tree, Bool, MerkleTree.MerkleTree, Blob)] = [
    (trees[0], true, Bitcoin.merkleTree(ls), Reference.bitcoin(ls)),
    (trees[1], false, Bagged.merkleTree(ls), Reference.bagged(ls)),
    (trees[2], false, ZeroPadded.merkleTree(ls, depth), Reference.padded(ls, depth)),
  ];
  for ((tree, checked, full, root) in kinds.values()) {
    // Refused up front: nothing is added and the count stays 0, but the
    // verifier fails.
    do {
      let p = full.rightPeaks(n);
      let bads : [([Blob], [Blob])] = [
        ([], p),
        (ls, [("short" : Blob)]),
        ([("short" : Blob)], p),
        (ls, Array.tabulate<Blob>(depth + 1, func(i) = leaf(900 + i))),
        (Array.tabulate<Blob>(2 ** depth + 1, func(i) = leaf(i)), []),
      ];
      for ((c, pr) in bads.values()) {
        let w = Chunks.onTree(root, tree, checked);
        assert not w.verifyChunk(c, pr) and w.broken() and w.count() == 0;
      };
    };

    // Honest chunks of every length pattern, one verifier after another on
    // the same tree.
    for (step in ([1, 2, 3, 5, 8, 1000] : [Nat]).values()) {
      let v = Chunks.onTree(root, tree, checked);
      assert v.count() == 0 and not v.broken();
      for (m2 in Fixtures.chunkEnds(n, step).values()) {
        let m = v.count().toNat();
        assert v.verifyChunk(slice(ls, m, m2), full.rightPeaks(m2)) and v.count() == m2.toNat64();
      };
      assert v.complete() and not v.broken();
      assert not v.verifyChunk([ls[0]], []);
    };

    // A forged leaf, at each chunk in turn: refused, and nothing after it
    // is accepted, not even the honest chunk.
    var cut = 0;
    while (cut < n) {
      let cut2 = if (cut + 5 >= n) n else cut + 5;
      let v = Chunks.onTree(root, tree, checked);
      if (cut > 0) assert v.verifyChunk(slice(ls, 0, cut), full.rightPeaks(cut));
      let chunk = slice(ls, cut, cut2);
      let p = full.rightPeaks(cut2);
      assert not v.verifyChunk(flipFirst(chunk), p);
      assert v.broken() and not v.complete();
      assert not v.verifyChunk(chunk, p);
      cut := cut2;
    };

    // A wrong peak fails it too.
    if (n > 1) {
      let v = Chunks.onTree(root, tree, checked);
      let p = full.rightPeaks(1);
      assert not v.verifyChunk([ls[0]], flipFirst(p));
      assert v.broken();
    };
  };
};

// The presets' own form.
//
// Their rules on the caller's tree, which serves one verifier after another.
let zTree = trees[2];
for (n in ([1, 2, 7, 23, 100] : [Nat]).values()) {
  let ls = leaves(n);
  let cut = (n + 1) / 2;
  let runs : [(Chunks.Verifier, MerkleTree.MerkleTree)] = [
    (Bitcoin.verifierOn(Reference.bitcoin(ls), trees[0]), Bitcoin.merkleTree(ls)),
    (Bagged.verifierOn(Reference.bagged(ls), trees[1]), Bagged.merkleTree(ls)),
    (ZeroPadded.verifierOn(Reference.padded(ls, depth), zTree), ZeroPadded.merkleTree(ls, depth)),
  ];
  for ((v, full) in runs.values()) {
    assert v.count() == 0 and not v.complete();
    assert v.verifyChunk(slice(ls, 0, cut), full.rightPeaks(cut));
    if (cut < n) assert v.verifyChunk(slice(ls, cut, n), []);
    assert v.count() == n.toNat64() and not v.broken();
  };
  // a zero-padded tree is complete only at its full depth
  assert runs[0].0.complete() and runs[1].0.complete();

  // As `new` does, these check for equal siblings in Bitcoin only.
  if (n >= 2) {
    let twice = Array.tabulate<Blob>(n, func(i) = if (i == 1) ls[0] else ls[i]);
    assert not Bitcoin.verifierOn(Reference.bitcoin(twice), trees[0]).verifyChunk(twice, []);
    assert Bagged.verifierOn(Reference.bagged(twice), trees[1]).verifyChunk(twice, []);
    assert ZeroPadded.verifierOn(Reference.padded(twice, depth), zTree).verifyChunk(twice, []);
  };
  // the tree of a zero-padded verifier is still the caller's tree
  assert zTree.count == n.toNat64();
};

// The proof length limit.
//
// A proof may have one peak per level and no more: 8 leaves, the first one
// sent alone, in a verifier of depth 3.
do {
  let eight = leaves(8);
  let full = Bitcoin.merkleTree(eight);
  let p = full.rightPeaks(1);
  assert p.size() == 3;
  let v = Bitcoin.verifier(Reference.bitcoin(eight), 3);
  assert not Bitcoin.verifier(Reference.bitcoin(eight), 3).verifyChunk([eight[0]], p.concat([leaf(999)]));
  assert v.verifyChunk([eight[0]], p);
  assert v.verifyChunk(slice(eight, 1, 8), []) and v.complete();
};

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
import Ssz "../../src/Ssz";
import Chunks "../../src/Chunks";
import Prove "../../src/Prove";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaf; leaves; slice; flipFirst } = Fixtures;

let depth = 9;
let padFill = Ssz.fillOf(depth);

// The trees of the caller: Bitcoin's is a double tree, the others single.
let trees = [Peaks.withDepth(depth, true), Peaks.withDepth(depth, false), Peaks.withDepth(depth, false)];
let sizes : [Nat] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 23, 31, 32, 33, 64, 100, 257];

// The rules of each format, given to `Chunks.onTree` directly.
for (n in sizes.values()) {
  let ls = leaves(n);
  let kinds : [(Peaks.Peaks, Peaks.Fill, Bool, [[Blob]], Blob)] = [
    (trees[0], #copy, true, Bitcoin.levels(ls), Reference.bitcoin(ls)),
    (trees[1], #skip, false, Bagged.levels(ls), Reference.bagged(ls)),
    (trees[2], padFill, false, Ssz.levels(ls, depth), Reference.padded(ls, depth)),
  ];
  for ((tree, fill, checked, levels, root) in kinds.values()) {
    // Refused up front: nothing is added and the count stays 0, but the
    // verifier fails.
    do {
      let p = Prove.rightPeaks(levels, n);
      let bads : [([Blob], [Blob])] = [
        ([], p),
        (ls, [("short" : Blob)]),
        ([("short" : Blob)], p),
        (ls, Array.tabulate<Blob>(depth + 1, func(i) = leaf(900 + i))),
        (Array.tabulate<Blob>(2 ** depth + 1, func(i) = leaf(i)), []),
      ];
      for ((c, pr) in bads.values()) {
        let w = Chunks.onTree(root, tree, fill, checked);
        assert not w.verifyChunk(c, pr) and w.broken() and w.count() == 0;
      };
    };

    // Honest chunks of every length pattern, one verifier after another on
    // the same tree.
    for (step in ([1, 2, 3, 5, 8, 1000] : [Nat]).values()) {
      let v = Chunks.onTree(root, tree, fill, checked);
      assert v.count() == 0 and not v.broken();
      for (m2 in Fixtures.chunkEnds(n, step).values()) {
        let m = v.count().toNat();
        assert v.verifyChunk(slice(ls, m, m2), Prove.rightPeaks(levels, m2)) and v.count() == m2.toNat64();
      };
      assert v.complete() and not v.broken();
      assert not v.verifyChunk([ls[0]], []);
    };

    // A forged leaf, at each chunk in turn: refused, and nothing after it
    // is accepted, not even the honest chunk.
    var cut = 0;
    while (cut < n) {
      let cut2 = if (cut + 5 >= n) n else cut + 5;
      let v = Chunks.onTree(root, tree, fill, checked);
      if (cut > 0) assert v.verifyChunk(slice(ls, 0, cut), Prove.rightPeaks(levels, cut));
      let chunk = slice(ls, cut, cut2);
      let p = Prove.rightPeaks(levels, cut2);
      assert not v.verifyChunk(flipFirst(chunk), p);
      assert v.broken() and not v.complete();
      assert not v.verifyChunk(chunk, p);
      cut := cut2;
    };

    // A wrong peak fails it too.
    if (n > 1) {
      let v = Chunks.onTree(root, tree, fill, checked);
      let p = Prove.rightPeaks(levels, 1);
      assert not v.verifyChunk([ls[0]], flipFirst(p));
      assert v.broken();
    };
  };
};

// The presets' own form.
//
// Their rules on the caller's tree, which serves one verifier after another.
let zTree = Ssz.new(depth);
for (n in ([1, 2, 7, 23, 100] : [Nat]).values()) {
  let ls = leaves(n);
  let cut = (n + 1) / 2;
  let runs : [(Chunks.Verifier, [[Blob]])] = [
    (Bitcoin.verifierOn(Reference.bitcoin(ls), trees[0]), Bitcoin.levels(ls)),
    (Bagged.verifierOn(Reference.bagged(ls), trees[1]), Bagged.levels(ls)),
    (Ssz.verifierOn(Reference.padded(ls, depth), zTree), Ssz.levels(ls, depth)),
  ];
  for ((v, levels) in runs.values()) {
    assert v.count() == 0 and not v.complete();
    assert v.verifyChunk(slice(ls, 0, cut), Prove.rightPeaks(levels, cut));
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
    assert Ssz.verifierOn(Reference.padded(twice, depth), zTree).verifyChunk(twice, []);
  };
  // the tree of a zero-padded verifier is still the caller's tree
  assert zTree.count() == n.toNat64();
};

// The proof length limit.
//
// A proof may have one peak per level and no more: 8 leaves, the first one
// sent alone, in a verifier of depth 3.
do {
  let eight = leaves(8);
  let levels = Bitcoin.levels(eight);
  let p = Prove.rightPeaks(levels, 1);
  assert p.size() == 3;
  let v = Bitcoin.verifier(Reference.bitcoin(eight), 3);
  assert not Bitcoin.verifier(Reference.bitcoin(eight), 3).verifyChunk([eight[0]], p.concat([leaf(999)]));
  assert v.verifyChunk([eight[0]], p);
  assert v.verifyChunk(slice(eight, 1, 8), []) and v.complete();
};

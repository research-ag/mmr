// @testmode wasi
// The chunk verifier on its own tree, for all three formats: honest chunk
// sequences are accepted, every kind of forgery is rejected and fails the
// verifier for good.
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Chunks "../../src/Chunks";
import Prove "../../src/Prove";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaf; leaves; slice; flip; flipFirst; depthFor } = Fixtures;

let depth = 9;

// Runs the whole battery of chunk sequences against one list.
//
// Random-looking chunk sequences are accepted chunk by chunk. A forged leaf,
// a dropped or wrong peak, a peak too many, a wrong root and a chunk after
// completion are rejected, and a rejected chunk fails the verifier for good.
//
// `make` creates a fresh verifier for a root. `minimal` tells whether the
// format's root is complete exactly when the last leaf is in (Bitcoin and
// bagged); a zero-padded tree is complete only at its full depth.
func battery(ls : [Blob], levels : [[Blob]], root : Blob, make : Blob -> Chunks.Verifier, minimal : Bool) {
  let n = ls.size();
  for (step in ([1, 2, 3, 5, 8, 1000] : [Nat]).values()) {
    let v = make(root);
    var m = 0;
    for (m2 in Fixtures.chunkEnds(n, step).values()) {
      let chunk = slice(ls, m, m2);
      let p = Prove.rightPeaks(levels, m2);

      // Each rejection is tried on a fresh verifier brought to the same
      // point. It must fail the verifier, which then rejects even the
      // honest chunk.
      func rejected(c : [Blob], proof : [Blob]) {
        let w = make(root);
        if (m > 0) assert w.verifyChunk(slice(ls, 0, m), Prove.rightPeaks(levels, m));
        assert not w.verifyChunk(c, proof);
        assert w.broken() and not w.complete();
        assert not w.verifyChunk(chunk, p);
      };
      rejected(chunk, p.concat([leaf(999)]));
      if (p.size() > 0) {
        rejected(chunk, slice(p, 1, p.size()));
        rejected(chunk, flipFirst(p));
      };
      rejected(flipFirst(chunk), p);
      rejected([], p);

      // the honest chunk is accepted
      assert not v.broken();
      assert v.count() == m.toNat64();
      assert v.verifyChunk(chunk, p);
      assert v.count() == m2.toNat64();
      if (minimal) assert v.complete() == (m2 == n);
      m := m2;
    };
    assert v.complete();
    // nothing is accepted after completion
    assert not v.verifyChunk([ls[0]], []);
  };
  assert not make(flip(root)).verifyChunk(ls, []);

  // Malformed input is rejected, not trapped on, and fails the verifier.
  for (bad in [(Array.tabulate<Blob>(n, func(i) = if (i == 0) ("short" : Blob) else ls[i]), [] : [Blob]), (ls, [("short" : Blob)])].values()) {
    let w = make(root);
    assert not w.verifyChunk(bad.0, bad.1) and w.broken();
  };
  assert make(root).verifyChunk(ls, []);
};

for (n in ([1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 23, 31, 32, 33, 64, 100, 257] : [Nat]).values()) {
  let ls = leaves(n);
  battery(ls, Bitcoin.levels(ls), Reference.bitcoin(ls), func(r) = Bitcoin.verifier(r, 10), true);
  battery(ls, Bagged.levels(ls), Reference.bagged(ls), func(r) = Bagged.verifier(r, 10), true);
  battery(ls, Ssz.levels(ls, depth), Reference.padded(ls, depth), func(r) = Ssz.verifier(r, depth), false);

  // More leaves than the verifier has room for are rejected.
  let d = depthFor(n);
  assert Bitcoin.verifier(Reference.bitcoin(ls), d).verifyChunk(ls, []);
  if (d > 0) assert not Bitcoin.verifier(Reference.bitcoin(ls), d - 1 : Nat).verifyChunk(ls, []);
};

// The known limit: a whole level verifies as a shorter list.
//
// A Merkle root does not say how deep the tree is. The 4 nodes of the level
// above the 8 leaves are, as a list of 4 leaves, a tree with the same root,
// and the verifier accepts them as such. The caller must know the leaf count
// from elsewhere.
do {
  let eight = leaves(8);
  let level1 = Array.tabulate<Blob>(4, func(i) = Reference.dsha(eight[2 * i], eight[2 * i + 1]));
  assert Bitcoin.merkleRoot(level1) == Reference.bitcoin(eight);
  let v = Bitcoin.verifier(Reference.bitcoin(eight), 10);
  assert v.verifyChunk(level1, []) and v.complete() and v.count() == 4;
};

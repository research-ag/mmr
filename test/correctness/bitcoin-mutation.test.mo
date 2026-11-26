// @testmode wasi
// Bitcoin's duplicate-node weakness: a list whose last 2^k leaves are
// written out twice has the same root as the list without the copy. The
// checked forms of the package (`addChecked`, `addPairChecked`, `mutated`
// and the chunk verifier) refuse such lists, and refuse equal siblings
// wherever they arise: in adding and in closing.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Chunks "../../src/Chunks";
import Prove "../../src/Prove";
import Nat "mo:core/Nat";
import Array "mo:core/Array";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaves; slice } = Fixtures;

// A caller's tree for the verifiers below.
let bare = Peaks.withDepth(10, true);

// Mutated lists.
//
// A mutated list has the same root as the original, the plain tree hashes
// it all the same, and the checked tree and the chunk verifier stop.
for (n in ([2, 3, 5, 6, 7, 11, 12, 13, 16, 100] : [Nat]).values()) {
  let ls = leaves(n);
  let root = Reference.bitcoin(ls);
  assert not Bitcoin.mutated(ls);
  var width = 1;
  while (width < n) {
    if (n % (2 * width) == width) {
      // the last `width` leaves written out twice: the same root
      let mutated = ls.concat(slice(ls, n - width, n));
      assert Reference.bitcoin(mutated) == root and Bitcoin.mutated(mutated);

      // the plain tree hashes it all the same; the checked one stops
      let plain = Bitcoin.new(2 * n);
      let checked = Bitcoin.new(2 * n);
      var ok = true;
      for (l in mutated.values()) {
        Bitcoin.add(plain, l);
        if (ok and not Bitcoin.addChecked(checked, l)) ok := false;
      };
      assert Bitcoin.root(plain) == root and not ok;

      // The chunk verifier rejects it, in one chunk and split anywhere. An
      // odd cut makes the second chunk start with a single leaf. Both on
      // its own tree and on the caller's.
      let levels = Bitcoin.levels(mutated);
      for (cut in Nat.range(1, mutated.size() + 1)) {
        for (v in [Bitcoin.verifier(root, 10), Chunks.onTree(root, bare, #copy, true)].values()) {
          if (cut == mutated.size()) {
            assert not v.verifyChunk(mutated, []);
          } else {
            assert not (v.verifyChunk(slice(mutated, 0, cut), Prove.rightPeaks(levels, cut)) and v.verifyChunk(slice(mutated, cut, mutated.size()), []));
          };
        };
      };
    };
    width *= 2;
  };
};

// Equal siblings, wherever they arise.
do {
  let t = leaves(6);
  let (a, b, c, d) = (t[0], t[1], t[2], t[3]);
  func h(x : Blob, y : Blob) : Blob = Reference.dsha(x, y);

  // Whether a verifier, on its own tree and on the caller's, rejects the
  // chunk and is failed by it.
  func rejects(list : [Blob], chunk : [Blob], proof : [Blob]) : Bool {
    let v = Bitcoin.verifier(Reference.bitcoin(list), 10);
    let w = Chunks.onTree(Reference.bitcoin(list), bare, #copy, true);
    not v.verifyChunk(chunk, proof) and v.broken() and not w.verifyChunk(chunk, proof) and w.broken();
  };

  // in adding: two leaves, and two nodes one level up
  assert rejects([a, a, b, c], [a, a, b, c], []);
  assert rejects([a, b, a, b, c, d], [a, b, a, b, c, d], []);

  // in closing, against a peak of the tree
  assert rejects([a, b, a, b], [a, b, a], [b]);

  // in closing, against a peak of the proof: at the lowest peak, and higher up
  assert rejects([a, b, a, b], [a, b], [h(a, b)]);
  assert rejects([a, b, c, d, a, b, c, d], [a, b, c], [d, h(h(a, b), h(c, d))]);
  assert rejects([a, a], [a], [a]);

  // An honest block: the proof may not name what Bitcoin would duplicate.
  let five = slice(t, 0, 5);
  let v5 = Bitcoin.verifier(Reference.bitcoin(five), 10);
  assert not Bitcoin.verifier(Reference.bitcoin(five), 10).verifyChunk(five, [t[4]]);
  assert v5.verifyChunk(five, []) and v5.complete();
  let v6 = Bitcoin.verifier(Reference.bitcoin(t), 10);
  assert not Bitcoin.verifier(Reference.bitcoin(t), 10).verifyChunk(t, [h(t[4], t[5])]);
  assert v6.verifyChunk(t, []) and v6.complete();

  // Pairs: the checked form refuses two equal leaves, and the same pair
  // twice, which would be two equal nodes one level up.
  let p = Peaks.new(8, true);
  assert not p.addPairChecked(a, a) and p.count == 0;
  assert p.addPairChecked(a, b) and p.count == 2;
  assert not p.addPairChecked(a, b) and p.count == 2;
  assert p.addPairChecked(c, d) and p.root(#copy) == Reference.bitcoin([a, b, c, d]);
};

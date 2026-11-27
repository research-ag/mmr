// @testmode wasi
// Building trees: the roots of all three formats against the references, by
// every way of adding leaves, and the saving and restoring of the peaks.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Prove "../../src/Prove";
import Hasher "mo:sha2/Hasher/Sha256";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Text "mo:core/Text";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaf; leaves; slice; depthFor } = Fixtures;

// The tree sizes to try: every size up to 40, and a few around the powers of
// two beyond.
let sizes : [Nat] = Array.tabulate<Nat>(40, func(i) = i + 1).concat([63, 64, 65, 100, 257]);

// The depth of the zero-padded trees: 512 places.
let depth = 9;

// Roots against the references, by every way of adding.
//
// For every size, the three presets must reproduce the references when
// filled leaf by leaf, one-shot, from hashers and from messages.
for (n in sizes.values()) {
  let ls = leaves(n);
  let bitcoin = Reference.bitcoin(ls);
  let bagged = Reference.bagged(ls);
  let padded = Reference.padded(ls, depth);

  // The presets, leaf by leaf. For small sizes the root is taken after
  // every leaf, to check each prefix of the list.
  let b = Bitcoin.new(n);
  let g = Bagged.new(n);
  let z = Ssz.new(depth);
  for (i in Nat.range(0, n)) {
    b.add(ls[i]);
    g.add(ls[i]);
    z.add(ls[i]);
    if (n <= 40) {
      let prefix = slice(ls, 0, i + 1);
      assert b.root() == Reference.bitcoin(prefix);
      assert g.root() == Reference.bagged(prefix);
      assert z.root() == Reference.padded(prefix, depth);
    };
  };
  assert b.root() == bitcoin and g.root() == bagged and z.root() == padded;
  // taking a root changes nothing
  assert b.root() == bitcoin;
  assert b.count() == n.toNat64() and g.count() == n.toNat64() and z.count() == n.toNat64();

  // One shot, adding in pairs.
  assert Bitcoin.merkleRoot(ls) == bitcoin;
  assert Bagged.merkleRoot(ls) == bagged;
  assert Ssz.merkleize(ls, ?(2 ** depth)) == padded;

  // The smallest depth: padded to the next power of two.
  let small = depthFor(n);
  assert Ssz.merkleize(ls, null) == Reference.padded(ls, small);
  assert g.peaks.root(#zeros({ table = Peaks.zeros(small, false); depth = null })) == Reference.padded(ls, small);

  // The prover's levels have the same roots.
  assert Prove.root(Bitcoin.levels(ls)) == bitcoin;
  assert Prove.root(Bagged.levels(ls)) == bagged;
  assert Prove.root(Ssz.levels(ls, depth)) == padded;

  // Leaves from hashers.
  let s = Peaks.new(n, true);
  let h = Hasher.new();
  for (l in ls.values()) { h.loadBlob32(l); s.addState(h) };
  assert s.root(#copy) == bitcoin;

  // Leaves from messages, hashed through a digest. A double tree's leaf is
  // the hash of the message once more, so its reference is the Bitcoin root
  // of the hashed leaves.
  let d = Sha256.new();
  let single = Peaks.new(n, false);
  let double = Peaks.new(n, true);
  for (i in Nat.range(0, n)) {
    let message = ("leaf" # i.toText()).encodeUtf8();
    single.addMessage(d, message);
    double.addMessage(d, message);
  };
  assert single.root(#skip) == bagged;
  assert double.root(#copy) == Reference.bitcoin(Array.tabulate<Blob>(n, func(i) = Sha256.fromBlob(ls[i])));
};

// `addAll` from any count.
//
// A list split anywhere into three runs gives the peaks of adding leaf by
// leaf, with and without the check for equal siblings.
for (n in ([1, 2, 3, 4, 5, 8, 9, 16, 17, 33] : [Nat]).values()) {
  let ls = leaves(n);
  let one = Peaks.new(n, true);
  for (l in ls.values()) one.add(l);
  let peaks = one.toBlobs();
  for (cut in Nat.range(0, n + 1)) {
    for (cut2 in ([cut, (cut + n) / 2, n] : [Nat]).values()) {
      for (checked in [false, true].values()) {
        let t = Peaks.new(n, true);
        assert t.addAll(ls, 0, cut, checked) and t.count == cut.toNat64();
        assert t.addAll(ls, cut, cut2, checked) and t.count == cut2.toNat64();
        assert t.addAll(ls, cut2, n, checked) and t.toBlobs() == peaks;
      };
    };
  };
  // An empty run adds nothing. A run inside the list adds only that run.
  let t = Peaks.new(n, false);
  assert t.addAll(ls, n, n, true) and t.count == 0;
  if (n >= 3) {
    assert t.addAll(ls, 1, n - 1 : Nat, false);
    assert t.root(#skip) == Reference.bagged(slice(ls, 1, n - 1 : Nat));
  };
};

// `addAll` with the check, exhaustively.
//
// For every list of up to 6 leaves over three values and every place to
// split it, the verdict is that of adding leaf by leaf, and an accepted list
// gives the same peaks.
do {
  let values = leaves(3);
  var lists = 0;
  var refused = 0;
  for (n in Nat.range(1, 7)) {
    for (code in Nat.range(0, 3 ** n)) {
      // the list that is the base 3 digits of `code`
      var c = code;
      let list = Array.tabulate<Blob>(n, func(_) { let v = values[c % 3]; c /= 3; v });
      let one = Peaks.new(8, true);
      var ok = true;
      for (l in list.values()) if (ok and not one.addChecked(l)) ok := false;
      for (cut in Nat.range(0, n)) {
        let t = Peaks.new(8, true);
        assert (t.addAll(list, 0, cut, true) and t.addAll(list, cut, n, true)) == ok;
        if (ok) assert t.toBlobs() == one.toBlobs();
      };
      lists += 1;
      if (not ok) refused += 1;
    };
  };
  // 3 + 9 + 27 + 81 + 243 + 729 lists, some refused and some accepted
  assert lists == 1092 and refused > 0 and refused < lists;
};

// `carry` at a height: a tree from the roots of subtrees.
//
// Adding the root of every aligned block of 2^k leaves at height k gives the
// same peaks as adding the leaves one by one.
for (n in ([8, 12, 16, 20, 100] : [Nat]).values()) {
  let ls = leaves(n);
  for (k in Nat.range(0, 3)) {
    let width = 2 ** k;
    if (n % width == 0) {
      let t = Peaks.new(n, true);
      for (j in Nat.range(0, n / width)) {
        t.spare().loadBlob32(Reference.bitcoin(slice(ls, j * width, (j + 1) * width)));
        t.carry(k.toNat64());
      };
      assert t.count == n.toNat64() and t.root(#copy) == Reference.bitcoin(ls);
      let u = Bitcoin.new(n);
      for (l in ls.values()) u.add(l);
      assert t.toBlobs() == u.peaks.toBlobs();
    };
  };
};

// Saving, exporting and restoring the peaks.
for (n in ([1, 2, 3, 7, 8, 21, 100] : [Nat]).values()) {
  let ls = leaves(n);
  let t = Peaks.new(200, true);
  for (l in ls.values()) t.add(l);
  let peaks = t.toBlobs();
  assert peaks.size() == Nat64.bitcountNonZero(n.toNat64()).toNat();

  // copy aside, grow, copy back
  let aside = Peaks.new(200, true);
  Peaks.copy(t, aside);
  t.add(leaf(1000));
  assert t.root(#copy) != aside.root(#copy);
  Peaks.copy(aside, t);
  assert t.count == n.toNat64() and t.root(#copy) == Reference.bitcoin(ls) and t.toBlobs() == peaks;

  // a fresh tree from the exported peaks goes on as the original does
  let u = Peaks.new(200, true);
  assert u.load(n.toNat64(), peaks);
  u.add(leaf(n));
  assert u.root(#copy) == Reference.bitcoin(leaves(n + 1));

  // malformed input is refused and changes nothing
  assert not u.load(n.toNat64() + 1, peaks.concat([leaf(0), leaf(1), leaf(2), leaf(3), leaf(4), leaf(5), leaf(6), leaf(7)]));
  assert not u.load(1000, []);
  assert not u.load(1, [("short" : Blob)]);
  assert u.count == n.toNat64() + 1;
};

// @testmode wasi
// The allocation claims of adding: adding leaves in any form allocates
// nothing. This holds for the core operations of `Peaks` and for the
// functions of the presets that wrap them.
//
// The counter behind the measurements is maintained only in compiled wasm,
// hence the wasi test mode.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Hasher "mo:sha2/Hasher/Sha256";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Text "mo:core/Text";
import Allocation "../support/Allocation";
import Fixtures "../support/Fixtures";

let { alloc; check } = Allocation;
let _ = Allocation.units(); // checks the harness

let n = 1000;
let depth = 10;
let ls = Fixtures.leaves(n);
let messages = Array.tabulate<Blob>(n, func(i) = ("leaf" # i.toText()).encodeUtf8());

// The core operations of `Peaks`.
//
// Each way of adding a leaf, 1000 times over, in a tree that was sized for
// it up front.
do {
  let t = Peaks.new(n, true);
  check("add", alloc(func() { var i = 0; while (i < n) { t.add(ls[i]); i += 1 } }), 0);
  let c = Peaks.new(n, true);
  check("addChecked", alloc(func() { var i = 0; while (i < n) { assert c.addChecked(ls[i]); i += 1 } }), 0);
  let p = Peaks.new(n, true);
  check("addPair", alloc(func() { var i = 0; while (i < n) { p.addPair(ls[i], ls[i + 1]); i += 2 } }), 0);
  let q = Peaks.new(n, true);
  check("addPairChecked", alloc(func() { var i = 0; while (i < n) { assert q.addPairChecked(ls[i], ls[i + 1]); i += 2 } }), 0);

  // from a hasher that holds the leaf, and from a message that a digest
  // hashes
  let s = Peaks.new(n, false);
  let h = Hasher.new();
  h.loadBlob32(ls[0]);
  check("addState", alloc(func() { var i = 0; while (i < n) { s.addState(h); i += 1 } }), 0);
  let m = Peaks.new(n, false);
  let d = Sha256.new();
  check("addMessage", alloc(func() { var i = 0; while (i < n) { m.addMessage(d, messages[i]); i += 1 } }), 0);
};

// `addAll`.
//
// A run of leaves, from an even and from an odd count, with and without the
// check for equal siblings.
do {
  for (checked in [false, true].values()) {
    let t = Peaks.new(n, true);
    check("addAll", alloc(func() { assert t.addAll(ls, 0, 301, checked) and t.addAll(ls, 301, n, checked) }), 0);
    assert t.count == 1000;
  };
};

// The functions of the presets, and the small accessors.
do {
  let b = Bitcoin.new(n);
  check("Bitcoin.add", alloc(func() { var i = 0; while (i < n) { b.add(ls[i]); i += 1 } }), 0);
  let c = Bitcoin.new(n);
  check("Bitcoin.addChecked", alloc(func() { var i = 0; while (i < n) { assert c.addChecked(ls[i]); i += 1 } }), 0);
  let g = Bagged.new(n);
  check("Bagged.add", alloc(func() { var i = 0; while (i < n) { g.add(ls[i]); i += 1 } }), 0);
  let m = Bagged.new(n);
  let d = Sha256.new();
  check("Bagged.addMessage", alloc(func() { var i = 0; while (i < n) { m.addMessage(d, messages[i]); i += 1 } }), 0);
  let z = Ssz.new(depth);
  check("Ssz.add", alloc(func() { var i = 0; while (i < n) { z.add(ls[i]); i += 1 } }), 0);
  check(
    "count, capacity, spare",
    alloc(
      func() {
        assert b.count() == 1000 and g.count() == 1000 and z.count() == 1000;
        assert b.peaks.capacity() >= 1000;
        ignore b.peaks.spare();
      }
    ),
    0,
  );
  check("Bitcoin.mutated", alloc(func() { assert not Bitcoin.mutated(ls) }), 0);
};

// `carry` at a height.
//
// The root of a subtree added as one peak, at the heights 0 to 3, with and
// without the check.
do {
  let t = Peaks.new(64, true);
  check(
    "carry at heights 0 to 3",
    alloc(
      func() {
        var k : Nat64 = 4;
        while (k > 0) {
          k -= 1;
          var j = 0;
          while (j < 3) {
            t.spare().loadBlob32(ls[j]);
            if (t.count % (1 << k) == 0) {
              if (j % 2 == 0) t.carry(k) else assert t.carryChecked(k);
            };
            j += 1;
          };
        };
      }
    ),
    0,
  );
  assert t.count > 0;
};

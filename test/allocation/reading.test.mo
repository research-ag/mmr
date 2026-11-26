// @testmode wasi
// The allocation claims of reading a tree: closing it and copying or loading
// its peaks allocate nothing, a root allocates only its `Blob`, and
// exporting the peaks allocates one `Blob` per peak and the array.
//
// The counter behind the measurements is maintained only in compiled wasm,
// hence the wasi test mode.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Prove "../../src/Prove";
import Nat64 "mo:core/Nat64";
import Nat "mo:core/Nat";
import Allocation "../support/Allocation";
import Fixtures "../support/Fixtures";

let { alloc; check } = Allocation;
let { readout; word } = Allocation.units();

let n = 1000;
let depth = 10;
let ls = Fixtures.leaves(n);

// Closing, roots and saving, in all three formats.
//
// At several sizes, closing with a proof and without, taking the root,
// copying the peaks aside and loading them from their blobs.
do {
  let padFill = Ssz.fillOf(depth);
  let kinds : [(Text, Bool, Peaks.Fill, [[Blob]])] = [
    ("Bitcoin", true, #copy, Bitcoin.levels(ls)),
    ("bagged", false, #skip, Bagged.levels(ls)),
    ("zero-padded", false, padFill, Ssz.levels(ls, depth)),
  ];
  for ((name, double, fill, levels) in kinds.values()) {
    let t = Peaks.new(2 ** depth, double);
    let aside = Peaks.new(2 ** depth, double);
    for (m in ([1, 2, 300, 617, 999, 1000] : [Nat]).values()) {
      while (t.count.toNat() < m) t.add(ls[t.count.toNat()]);
      let proof = Prove.rightPeaks(levels, m);
      check(name # ": close with a proof, " # m.toText(), alloc(func() { assert t.close(proof, fill, true) }), 0);
      check(name # ": close, " # m.toText(), alloc(func() { assert t.close([], fill, false) }), 0);
      check(name # ": root, " # m.toText(), alloc(func() { ignore t.root(fill) }), readout);
      check(name # ": copy, " # m.toText(), alloc(func() { Peaks.copy(t, aside) }), 0);
      let peaks = t.toBlobs();
      check(name # ": load, " # m.toText(), alloc(func() { assert aside.load(t.count, peaks) }), 0);
    };
  };
};

// The roots of the presets: one `Blob` each.
do {
  let b = Bitcoin.new(n);
  let g = Bagged.new(n);
  let z = Ssz.new(depth);
  for (l in ls.values()) { Bitcoin.add(b, l); Bagged.add(g, l); Ssz.add(z, l) };
  check("Bitcoin.root", alloc(func() { ignore Bitcoin.root(b) }), readout);
  check("Bagged.root", alloc(func() { ignore Bagged.root(g) }), readout);
  check("Ssz.root", alloc(func() { ignore Ssz.root(z) }), readout);
};

// Mixing in the length.
//
// A small constant: one hasher and the result, nothing for the length
// chunk, whatever the length.
do {
  let { oneHasher } = Allocation.units();
  let root = ls[0];
  let mix = alloc(func() { ignore Ssz.mixInLength(root, 0) });
  assert mix > 0;
  check("mixInLength, 5", alloc(func() { ignore Ssz.mixInLength(root, 5) }), mix);
  check("mixInLength, 2^40", alloc(func() { ignore Ssz.mixInLength(root, 1_099_511_627_776) }), mix);
  check("mixInLength, 2^64 - 1", alloc(func() { ignore Ssz.mixInLength(root, 18_446_744_073_709_551_615) }), mix);
  check("mixInLength", mix, oneHasher + readout);
  for (k in ([0, 1, 7, 1000] : [Nat]).values()) {
    let z = Ssz.new(depth);
    for (i in Nat.range(0, k)) z.add(ls[i]);
    check("Ssz.rootWithLength, " # k.toText() # " chunks", alloc(func() { ignore z.rootWithLength() }), readout + mix);
  };
};

// Exporting the peaks.
//
// One `Blob` per peak, and the array that holds them.
do {
  let t = Peaks.new(n, true);
  let empty = alloc(func() { ignore t.toBlobs() });
  for (k in ([1, 2, 3, 7, 8, 1000] : [Nat]).values()) {
    while (t.count.toNat() < k) t.add(ls[t.count.toNat()]);
    let peaks = Nat64.bitcountNonZero(t.count).toNat();
    check("toBlobs, " # k.toText() # " leaves", alloc(func() { ignore t.toBlobs() }), empty + peaks * (readout + word));
  };
};

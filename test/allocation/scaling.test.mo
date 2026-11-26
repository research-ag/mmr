// @testmode wasi
// Nothing grows with the number of leaves: what the package allocates
// depends on the depth of a tree and never on the count of its leaves, and
// sizing a tree never computes with large numbers.
//
// The counter behind the measurements is maintained only in compiled wasm,
// hence the wasi test mode.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Chunks "../../src/Chunks";
import Prove "../../src/Prove";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Allocation "../support/Allocation";
import Fixtures "../support/Fixtures";

let { alloc; check } = Allocation;
let { readout; oneHasher; word; pool0 } = Allocation.units();

// A larger tree than elsewhere, across the long carry at 4096 leaves.
let big = Array.tabulate<Blob>(5000, func(i) = Fixtures.leaf(10_000 + i));

// A larger tree.
//
// Still nothing for adding, the same single `Blob` for a root, and nothing
// for a chunk of 5000 leaves.
do {
  for (double in [false, true].values()) {
    let t = Peaks.new(5000, double);
    check("add, 5000 leaves", alloc(func() { var i = 0; while (i < 5000) { t.add(big[i]); i += 1 } }), 0);
    check("root, 5000 leaves", alloc(func() { ignore t.root(#copy) }), readout);
    check("close, 5000 leaves", alloc(func() { assert t.close([], #skip, true) }), 0);
  };
  let levels = Bitcoin.levels(big);
  let v = Bitcoin.verifier(Prove.root(levels), 13);
  check("verifyChunk, 5000 leaves in one chunk", alloc(func() { assert v.verifyChunk(big, []) }), 0);
};

// The one-shot roots.
//
// They allocate their pool and the root, and nothing per leaf: exactly what
// `new` for that many leaves allocates, plus the `Blob`. The pool itself
// grows by one hasher each time the leaf count doubles.
do {
  for (k in ([1, 2, 3, 600, 1000, 1024, 2000, 5000] : [Nat]).values()) {
    let part = Array.tabulate<Blob>(k, func(i) = big[i]);
    let suffix = ", " # k.toText() # " leaves";
    let pool = alloc(func() { ignore Peaks.new(k, true) });
    // The root of a single leaf is the leaf: nothing is made at all.
    let oneShot = if (k == 1) 0 else pool + readout;
    check("Bitcoin.merkleRoot" # suffix, alloc(func() { ignore Bitcoin.merkleRoot(part) }), oneShot);
    check("Bagged.merkleRoot" # suffix, alloc(func() { ignore Bagged.merkleRoot(part) }), oneShot);
    let d = Fixtures.depthFor(k);
    let padded = alloc(func() { ignore Ssz.new(d) });
    check("Ssz.merkleize" # suffix, alloc(func() { ignore Ssz.merkleize(part, null) }), padded + readout);
  };
  // 1000 and 600 leaves need the same depth, so the same pool
  check("the pool for 1000 and for 600 leaves", alloc(func() { ignore Peaks.new(1000, true) }), alloc(func() { ignore Peaks.new(600, true) }));
  assert alloc(func() { ignore Peaks.new(5000, true) }) > alloc(func() { ignore Peaks.new(1000, true) });
};

// Sizing a tree.
//
// It computes no power and no product of large numbers: a capacity given as
// a number of leaves costs what the same depth costs. The cost of a depth
// is the smallest tree plus one hasher and one slot per level.
do {
  for (d in ([0, 1, 10, 32, 40, 60, 61] : [Nat]).values()) {
    let byDepth = alloc(func() { ignore Peaks.withDepth(d, true) });
    let leaves = Nat.bitshiftLeft(1, d.toNat32());
    // 2^61 is itself a big number; reading it costs one 72-byte conversion.
    let reading = if (d <= 60) 0 else 72;
    check("Peaks.new for 2^" # d.toText() # " leaves", alloc(func() { ignore Peaks.new(leaves, true) }), byDepth + reading);
    check("Peaks.withDepth, " # d.toText(), byDepth, pool0 + d * (oneHasher + word));
  };

  // SSZ limits are large powers of two: 2^40 for the validator registry.
  let few = Array.tabulate<Blob>(5, func(i) = big[i]);
  let registry = alloc(func() { ignore Ssz.new(40) });
  check("Ssz.merkleize with a limit of 2^40", alloc(func() { ignore Ssz.merkleize(few, ?1_099_511_627_776) }), registry + readout);
};

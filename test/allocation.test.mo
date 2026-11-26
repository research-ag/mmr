// @testmode wasi
// The allocation claims of the package: adding leaves, closing a tree,
// verifying a chunk and saving the peaks allocate nothing; a root allocates
// only its `Blob`.
//
// `Prim.rts_total_allocation()` counts all bytes ever allocated, so its
// difference around a piece of code is what that code allocated. It is
// maintained only in compiled wasm, hence the wasi test mode.
import Peaks "../src/Peaks";
import Bitcoin "../src/Bitcoin";
import Bagged "../src/Bagged";
import Ssz "../src/Ssz";
import Chunks "../src/Chunks";
import Prove "../src/Prove";
import Hasher "mo:sha2/Hasher/Sha256";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Text "mo:core/Text";
import Prim "mo:prim";

func alloc(f : () -> ()) : Nat {
  let before = Prim.rts_total_allocation();
  f();
  Prim.rts_total_allocation() - before;
};
func check(name : Text, actual : Nat, expected : Nat) {
  if (actual != expected) {
    Prim.debugPrint(name # ": allocated " # actual.toText() # " bytes, expected " # expected.toText());
    assert false;
  };
};

// The harness itself: an empty closure allocates nothing, and the two sizes
// that the expectations below are made of.
check("harness", alloc(func() {}), 0);
let probe = Hasher.new();
let readout = alloc(func() { ignore probe.readSum() }); // a root as a Blob
let oneHasher = alloc(func() { ignore Hasher.new() });
let word = alloc(func() { ignore Prim.Array_init<Nat>(2, 0) }) - alloc(func() { ignore Prim.Array_init<Nat>(1, 0) }) : Nat; // an array slot
let pool0 = alloc(func() { ignore Peaks.withDepth(0, true) }); // the smallest tree
assert readout > 0 and oneHasher > 0;

func leaf(i : Nat) : Blob = Sha256.fromBlob(("leaf" # i.toText()).encodeUtf8());
let n = 1000;
let ls = Array.tabulate<Blob>(n, leaf);
let messages = Array.tabulate<Blob>(n, func(i) = ("leaf" # i.toText()).encodeUtf8());
let depth = 10;

// --- Adding ---
do {
  let t = Peaks.new(n, true);
  check("add", alloc(func() { var i = 0; while (i < n) { t.add(ls[i]); i += 1 } }), 0);
  let c = Peaks.new(n, true);
  check("addChecked", alloc(func() { var i = 0; while (i < n) { assert c.addChecked(ls[i]); i += 1 } }), 0);
  let p = Peaks.new(n, true);
  check("addPair", alloc(func() { var i = 0; while (i < n) { p.addPair(ls[i], ls[i + 1]); i += 2 } }), 0);
  let q = Peaks.new(n, true);
  check("addPairChecked", alloc(func() { var i = 0; while (i < n) { assert q.addPairChecked(ls[i], ls[i + 1]); i += 2 } }), 0);
  let s = Peaks.new(n, false);
  let h = Hasher.new();
  h.loadBlob32(ls[0]);
  check("addState", alloc(func() { var i = 0; while (i < n) { s.addState(h); i += 1 } }), 0);
  let m = Peaks.new(n, false);
  let d = Sha256.new();
  check("addMessage", alloc(func() { var i = 0; while (i < n) { m.addMessage(d, messages[i]); i += 1 } }), 0);
};

// --- Closing, roots, saving ---
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

  // the presets' roots
  let b = Bitcoin.new(n);
  let g = Bagged.new(n);
  let z = Ssz.new(depth);
  for (l in ls.values()) { Bitcoin.add(b, l); Bagged.add(g, l); Ssz.add(z, l) };
  check("Bitcoin.root", alloc(func() { ignore Bitcoin.root(b) }), readout);
  check("Bagged.root", alloc(func() { ignore Bagged.root(g) }), readout);
  check("Ssz.root", alloc(func() { ignore Ssz.root(z) }), readout);
};

// --- Branches ---
do {
  let levels = Bitcoin.levels(ls);
  let root = Prove.root(levels);
  let branch = Prove.branch(levels, 617, #copy);
  let node = Hasher.new();
  node.loadBlob32(ls[617]);
  check("foldBranch", alloc(func() { Peaks.foldBranch(node, 617, branch, true) }), 0);
  assert node.equalsBlob32(root);
  // the verifying functions make one hasher of their own
  check("Bitcoin.verifyBranch", alloc(func() { assert Bitcoin.verifyBranch(ls[617], 617, branch, root) }), oneHasher);
  let gLevels = Bagged.levels(ls);
  let path = Prove.branch(gLevels, 617, #skip);
  check("Bagged.verifyInclusion", alloc(func() { assert Bagged.verifyInclusion(ls[617], 617, n, path, Prove.root(gLevels)) }), oneHasher);
};

// --- The chunk verifier, accepting and rejecting ---
do {
  let bounds : [Nat] = [1, 2, 300, 617, 999, 1000];
  let kinds : [(Text, [[Blob]], Blob -> Chunks.Verifier)] = [
    ("Bitcoin", Bitcoin.levels(ls), func(r) = Bitcoin.verifier(r, depth)),
    ("bagged", Bagged.levels(ls), func(r) = Bagged.verifier(r, depth)),
    ("zero-padded", Ssz.levels(ls, depth), func(r) = Ssz.verifier(r, depth)),
  ];
  for ((name, levels, make) in kinds.values()) {
    let v = make(Prove.root(levels));
    var m = 0;
    for (m2 in bounds.values()) {
      let chunk = Array.tabulate<Blob>(m2 - m, func(i) = ls[m + i]);
      let forged = Array.tabulate<Blob>(m2 - m, func(i) = if (i == 0) ls[(m + 500) % n] else ls[m + i]);
      let proof = Prove.rightPeaks(levels, m2);
      // a rejection fails a verifier, so a spare one takes it
      let spare = make(Prove.root(levels));
      check(name # ": verifyChunk rejected, to " # m2.toText(), alloc(func() { assert not spare.verifyChunk(forged, proof) }), 0);
      check(name # ": verifyChunk, to " # m2.toText(), alloc(func() { assert v.verifyChunk(chunk, proof) }), 0);
      m := m2;
    };
    assert v.complete();
  };
};

// --- The verifier itself, and one on a caller's tree ---
do {
  let levels = Bitcoin.levels(ls);
  let root = Prove.root(levels);
  let tree = Peaks.withDepth(depth, true);
  // On a caller's tree a verifier is one small record, whatever the depth.
  let record = alloc(func() { ignore Chunks.onTree(root, tree, #copy, true) });
  assert record > 0 and record <= 128; // six fields, two of them mutable
  let deep = Peaks.withDepth(40, true);
  check("Chunks.onTree, depth 40", alloc(func() { ignore Chunks.onTree(root, deep, #copy, true) }), record);
  // The presets' form is the same record; the zero-padded one reuses the
  // table of its tree.
  check("Bitcoin.verifierOn", alloc(func() { ignore Bitcoin.verifierOn(root, tree) }), record);
  let single = Peaks.withDepth(depth, false);
  check("Bagged.verifierOn", alloc(func() { ignore Bagged.verifierOn(root, single) }), record);
  let padded = Ssz.new(depth);
  check("Ssz.verifierOn", alloc(func() { ignore Ssz.verifierOn(root, padded) }), record);
  // `new` makes the tree as well.
  let pool = alloc(func() { ignore Peaks.withDepth(depth, true) });
  check("Chunks.new", alloc(func() { ignore Chunks.new(root, depth, true, #copy, true) }), pool + record);
  check("Bitcoin.verifier", alloc(func() { ignore Bitcoin.verifier(root, depth) }), pool + record);

  // Chunks at odd and even offsets, accepted; then a forged one, which
  // breaks the verifier; then refusals.
  let v = Chunks.onTree(root, tree, #copy, true);
  var m = 0;
  for (m2 in ([1, 2, 300, 617] : [Nat]).values()) {
    let chunk = Array.tabulate<Blob>(m2 - m, func(i) = ls[m + i]);
    let proof = Prove.rightPeaks(levels, m2);
    check("verifyChunk, to " # m2.toText(), alloc(func() { assert v.verifyChunk(chunk, proof) }), 0);
    m := m2;
  };
  let rest = Array.tabulate<Blob>(n - m, func(i) = ls[m + i]);
  let forged = Array.tabulate<Blob>(n - m, func(i) = if (i == 7) ls[0] else ls[m + i]);
  let long = Array.tabulate<Blob>(depth + 1, func(i) = ls[i]);
  check("too long a proof", alloc(func() { assert not v.verifyChunk(rest, long) }), 0);
  check("verifyChunk rejected", alloc(func() { assert not v.verifyChunk(forged, []) }), 0);
  check("broken", alloc(func() { assert v.broken() and not v.verifyChunk(rest, []) }), 0);

  // addAll: nothing, from an even and from an odd count, with and without
  // the check.
  for (checked in [false, true].values()) {
    let t = Peaks.new(n, true);
    check("addAll", alloc(func() { assert t.addAll(ls, 0, 301, checked) and t.addAll(ls, 301, n, checked) }), 0);
    assert t.count == 1000;
  };
};

// --- The presets' own functions, and the small accessors ---
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

  // a carry at a height: the root of a subtree as one peak
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

// --- Nothing grows with the number of leaves ---
// A larger tree, across the long carry at 4096 leaves: still nothing for the
// adding, the same single Blob for a root, and nothing for a chunk of 5000.
do {
  let big = Array.tabulate<Blob>(5000, func(i) = leaf(10_000 + i));
  for (double in [false, true].values()) {
    let t = Peaks.new(5000, double);
    check("add, 5000 leaves", alloc(func() { var i = 0; while (i < 5000) { t.add(big[i]); i += 1 } }), 0);
    check("root, 5000 leaves", alloc(func() { ignore t.root(#copy) }), readout);
    check("close, 5000 leaves", alloc(func() { assert t.close([], #skip, true) }), 0);
  };
  let levels = Bitcoin.levels(big);
  let v = Bitcoin.verifier(Prove.root(levels), 13);
  check("verifyChunk, 5000 leaves in one chunk", alloc(func() { assert v.verifyChunk(big, []) }), 0);

  // The one-shot roots allocate their pool and the root, and nothing per
  // leaf: exactly what `new` for that many leaves allocates, plus the Blob.
  // The pool itself grows by one hasher each time the leaf count doubles.
  for (k in ([1, 2, 3, 600, 1000, 1024, 2000, 5000] : [Nat]).values()) {
    let part = Array.tabulate<Blob>(k, func(i) = big[i]);
    let suffix = ", " # k.toText() # " leaves";
    let pool = alloc(func() { ignore Peaks.new(k, true) });
    // The root of a single leaf is the leaf: nothing is made at all.
    let oneShot = if (k == 1) 0 else pool + readout;
    check("Bitcoin.merkleRoot" # suffix, alloc(func() { ignore Bitcoin.merkleRoot(part) }), oneShot);
    check("Bagged.merkleRoot" # suffix, alloc(func() { ignore Bagged.merkleRoot(part) }), oneShot);
    var d = 0;
    while (2 ** d < k) d += 1;
    let padded = alloc(func() { ignore Ssz.new(d) });
    check("Ssz.merkleize" # suffix, alloc(func() { ignore Ssz.merkleize(part, null) }), padded + readout);
  };
  check("the pool for 1000 and for 600 leaves", alloc(func() { ignore Peaks.new(1000, true) }), alloc(func() { ignore Peaks.new(600, true) }));
  // Sizing a tree computes no power and no product of large numbers: a
  // capacity given as a number of leaves costs what the same depth costs.
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
  assert alloc(func() { ignore Peaks.new(5000, true) }) > alloc(func() { ignore Peaks.new(1000, true) });
};

// --- Proof verification: one hasher, whatever the tree size and position ---
do {
  let messagesHash = Sha256.fromBlob("no root at all");
  for (k in ([1, 2, 5, 1000] : [Nat]).values()) {
    let part = Array.tabulate<Blob>(k, func(i) = ls[i]);
    let bLevels = Bitcoin.levels(part);
    let gLevels = Bagged.levels(part);
    let zLevels = Ssz.levels(part, depth);
    let (bRoot, gRoot, zRoot) = (Prove.root(bLevels), Prove.root(gLevels), Prove.root(zLevels));
    let fill = Ssz.fillOf(depth);
    for (i in ([0, k / 2, k - 1] : [Nat]).values()) {
      let suffix = ", leaf " # i.toText() # " of " # k.toText();
      let bb = Prove.branch(bLevels, i, #copy);
      check("Bitcoin.verifyBranch" # suffix, alloc(func() { assert Bitcoin.verifyBranch(part[i], i, bb, bRoot) }), oneHasher);
      let gp = Prove.branch(gLevels, i, #skip);
      check("Bagged.verifyInclusion" # suffix, alloc(func() { assert Bagged.verifyInclusion(part[i], i, k, gp, gRoot) }), oneHasher);
      let zb = Prove.branch(zLevels, i, fill);
      check("Ssz.verifyBranch" # suffix, alloc(func() { assert Ssz.verifyBranch(part[i], i, zb, zRoot) }), oneHasher);
      // a failing proof costs no more
      check("Bitcoin.verifyBranch, failing" # suffix, alloc(func() { assert not Bitcoin.verifyBranch(part[i], i, bb, messagesHash) }), oneHasher);
    };
  };
};

// --- Mixing in the length: a small constant ---
do {
  let root = ls[0];
  let mix = alloc(func() { ignore Ssz.mixInLength(root, 0) });
  assert mix > 0;
  check("mixInLength, 5", alloc(func() { ignore Ssz.mixInLength(root, 5) }), mix);
  check("mixInLength, 2^40", alloc(func() { ignore Ssz.mixInLength(root, 1_099_511_627_776) }), mix);
  check("mixInLength, 2^64 - 1", alloc(func() { ignore Ssz.mixInLength(root, 18_446_744_073_709_551_615) }), mix);
  // one hasher and the result, nothing for the length chunk
  check("mixInLength", mix, oneHasher + readout);
  for (k in ([0, 1, 7, 1000] : [Nat]).values()) {
    let z = Ssz.new(depth);
    for (i in Nat.range(0, k)) z.add(ls[i]);
    check("Ssz.rootWithLength, " # k.toText() # " chunks", alloc(func() { ignore z.rootWithLength() }), readout + mix);
  };
};

// --- Exporting the peaks: one Blob per peak, and the array ---
do {
  let t = Peaks.new(n, true);
  let empty = alloc(func() { ignore t.toBlobs() });
  for (k in ([1, 2, 3, 7, 8, 1000] : [Nat]).values()) {
    while (t.count.toNat() < k) t.add(ls[t.count.toNat()]);
    let peaks = Nat64.bitcountNonZero(t.count).toNat();
    check("toBlobs, " # k.toText() # " leaves", alloc(func() { ignore t.toBlobs() }), empty + peaks * (readout + word));
  };
};

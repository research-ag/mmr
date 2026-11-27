// @testmode wasi
// The allocation claims of verifying: a proof is verified with one hasher
// whatever the tree size and the position, a chunk is verified with nothing
// at all, and a verifier on a caller's tree is one small record.
//
// The counter behind the measurements is maintained only in compiled wasm,
// hence the wasi test mode.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Chunks "../../src/Chunks";
import Prove "../../src/Prove";
import Hasher "mo:sha2/Hasher/Sha256";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Text "mo:core/Text";
import Allocation "../support/Allocation";
import Fixtures "../support/Fixtures";

let { alloc; check } = Allocation;
let { oneHasher } = Allocation.units();

let n = 1000;
let depth = 10;
let ls = Fixtures.leaves(n);

// Branches.
//
// Folding a branch allocates nothing. The verifying functions make one
// hasher of their own.
do {
  let levels = Bitcoin.levels(ls);
  let root = Prove.root(levels);
  let branch = Prove.branch(levels, 617, #copy);
  let node = Hasher.new();
  node.loadBlob32(ls[617]);
  check("foldBranch", alloc(func() { Peaks.foldBranch(node, 617, branch, true) }), 0);
  assert node.equalsBlob32(root);
  check("Bitcoin.verifyBranch", alloc(func() { assert Bitcoin.verifyBranch(ls[617], 617, branch, root) }), oneHasher);
  let gLevels = Bagged.levels(ls);
  let path = Prove.branch(gLevels, 617, #skip);
  check("Bagged.verifyInclusion", alloc(func() { assert Bagged.verifyInclusion(ls[617], 617, n, path, Prove.root(gLevels)) }), oneHasher);
};

// Inclusion proofs: one hasher, whatever the tree size and position.
//
// A failing proof costs no more than a passing one.
do {
  let noRoot = Sha256.fromBlob("no root at all");
  let fill = Ssz.fillOf(depth);
  for (k in ([1, 2, 5, 1000] : [Nat]).values()) {
    let part = Array.tabulate<Blob>(k, func(i) = ls[i]);
    let bLevels = Bitcoin.levels(part);
    let gLevels = Bagged.levels(part);
    let zLevels = Ssz.levels(part, depth);
    let (bRoot, gRoot, zRoot) = (Prove.root(bLevels), Prove.root(gLevels), Prove.root(zLevels));
    for (i in ([0, k / 2, k - 1] : [Nat]).values()) {
      let suffix = ", leaf " # i.toText() # " of " # k.toText();
      let bb = Prove.branch(bLevels, i, #copy);
      check("Bitcoin.verifyBranch" # suffix, alloc(func() { assert Bitcoin.verifyBranch(part[i], i, bb, bRoot) }), oneHasher);
      let gp = Prove.branch(gLevels, i, #skip);
      check("Bagged.verifyInclusion" # suffix, alloc(func() { assert Bagged.verifyInclusion(part[i], i, k, gp, gRoot) }), oneHasher);
      let zb = Prove.branch(zLevels, i, fill);
      check("Ssz.verifyBranch" # suffix, alloc(func() { assert Ssz.verifyBranch(part[i], i, zb, zRoot) }), oneHasher);
      check("Bitcoin.verifyBranch, failing" # suffix, alloc(func() { assert not Bitcoin.verifyBranch(part[i], i, bb, noRoot) }), oneHasher);
    };
  };
};

// The chunk verifier, accepting and rejecting.
//
// Verifying a chunk allocates nothing, whether it is accepted or rejected.
// A rejection fails a verifier, so a spare one takes it.
do {
  let kinds : [(Text, [[Blob]], Blob -> Chunks.Verifier)] = [
    ("Bitcoin", Bitcoin.levels(ls), func(r) = Bitcoin.verifier(r, depth)),
    ("bagged", Bagged.levels(ls), func(r) = Bagged.verifier(r, depth)),
    ("zero-padded", Ssz.levels(ls, depth), func(r) = Ssz.verifier(r, depth)),
  ];
  for ((name, levels, make) in kinds.values()) {
    let v = make(Prove.root(levels));
    var m = 0;
    for (m2 in ([1, 2, 300, 617, 999, 1000] : [Nat]).values()) {
      let chunk = Array.tabulate<Blob>(m2 - m, func(i) = ls[m + i]);
      let forged = Array.tabulate<Blob>(m2 - m, func(i) = if (i == 0) ls[(m + 500) % n] else ls[m + i]);
      let proof = Prove.rightPeaks(levels, m2);
      let spare = make(Prove.root(levels));
      check(name # ": verifyChunk rejected, to " # m2.toText(), alloc(func() { assert not spare.verifyChunk(forged, proof) }), 0);
      check(name # ": verifyChunk, to " # m2.toText(), alloc(func() { assert v.verifyChunk(chunk, proof) }), 0);
      m := m2;
    };
    assert v.complete();
  };
};

// The verifier itself, and one on a caller's tree.
//
// On a caller's tree a verifier is one small record, whatever the depth.
// The presets' form is the same record. One that makes its own tree costs
// the tree as well.
do {
  let levels = Bitcoin.levels(ls);
  let root = Prove.root(levels);
  let tree = Peaks.withDepth(depth, true);
  let record = alloc(func() { ignore Chunks.onTree(root, tree, #copy, true) });
  assert record > 0 and record <= 128; // six fields, two of them mutable
  let deep = Peaks.withDepth(40, true);
  check("Chunks.onTree, depth 40", alloc(func() { ignore Chunks.onTree(root, deep, #copy, true) }), record);

  // the zero-padded form reuses the table of its tree
  check("Bitcoin.verifierOn", alloc(func() { ignore Bitcoin.verifierOn(root, tree) }), record);
  let single = Peaks.withDepth(depth, false);
  check("Bagged.verifierOn", alloc(func() { ignore Bagged.verifierOn(root, single) }), record);
  let padded = Ssz.new(depth);
  check("Ssz.verifierOn", alloc(func() { ignore Ssz.verifierOn(root, padded) }), record);

  // `new` makes the tree as well
  let pool = alloc(func() { ignore Peaks.withDepth(depth, true) });
  check("Chunks.new", alloc(func() { ignore Chunks.new(root, depth, true, #copy, true) }), pool + record);
  check("Bitcoin.verifier", alloc(func() { ignore Bitcoin.verifier(root, depth) }), pool + record);

  // Chunks at odd and even offsets are accepted with nothing allocated.
  let v = Chunks.onTree(root, tree, #copy, true);
  var m = 0;
  for (m2 in ([1, 2, 300, 617] : [Nat]).values()) {
    let chunk = Array.tabulate<Blob>(m2 - m, func(i) = ls[m + i]);
    let proof = Prove.rightPeaks(levels, m2);
    check("verifyChunk, to " # m2.toText(), alloc(func() { assert v.verifyChunk(chunk, proof) }), 0);
    m := m2;
  };

  // Then a forged chunk, which fails the verifier, and refusals, which
  // allocate nothing either.
  let rest = Array.tabulate<Blob>(n - m, func(i) = ls[m + i]);
  let forged = Array.tabulate<Blob>(n - m, func(i) = if (i == 7) ls[0] else ls[m + i]);
  let long = Array.tabulate<Blob>(depth + 1, func(i) = ls[i]);
  check("too long a proof", alloc(func() { assert not v.verifyChunk(rest, long) }), 0);
  check("verifyChunk rejected", alloc(func() { assert not v.verifyChunk(forged, []) }), 0);
  check("broken", alloc(func() { assert v.broken() and not v.verifyChunk(rest, []) }), 0);
};

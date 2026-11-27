// @testmode wasi
// Proofs: closing a prefix of a tree with the peaks to its right, and the
// inclusion proofs of all three formats, accepting and rejecting.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import ZeroPadded "../../src/ZeroPadded";
import MerkleTree "../../src/MerkleTree";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Hasher "mo:sha2/Hasher/Sha256";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaf; leaves; slice; flip } = Fixtures;

let sizes : [Nat] = Array.tabulate<Nat>(40, func(i) = i + 1).concat([63, 64, 65, 100, 257]);
let depth = 9;

// Closing a prefix with the peaks to its right.
//
// For every prefix of every list, the prover's peaks complete the prefix's
// tree to the root of the whole list, for all three formats. A peak too few,
// a peak too many and a wrong peak all give another root.
for (n in sizes.values()) {
  if (n <= 40) {
    let ls = leaves(n);
    let kinds : [(MerkleTree.MerkleTree, Blob)] = [
      (Bitcoin.merkleTree(ls), Reference.bitcoin(ls)),
      (Bagged.merkleTree(ls), Reference.bagged(ls)),
      (ZeroPadded.merkleTree(ls, depth), Reference.padded(ls, depth)),
    ];
    for ((full, root) in kinds.values()) {
      // the empty prefix is the whole root, the whole list needs no peaks
      assert full.rightPeaks(0) == [root] and full.rightPeaks(n) == [];
      let t = Peaks.new(2 ** depth, full.double, full.fill);
      for (m in Nat.range(1, n + 1)) {
        t.add(ls[m - 1]);
        let proof = full.rightPeaks(m);
        assert t.close(proof, false) and t.spare().readSum() == root;
        if (proof.size() > 0) {
          ignore t.close(slice(proof, 1, proof.size()), false);
          assert t.spare().readSum() != root;
          ignore t.close(Fixtures.flipFirst(proof), false);
          assert t.spare().readSum() != root;
        };
        ignore t.close(proof.concat([leaf(999)]), false);
        assert t.spare().readSum() != root;
      };
    };
  };
};

// Inclusion proofs.
//
// Every leaf of every list has a proof that verifies, and that does not
// verify for a changed leaf, root, position or proof.
for (n in sizes.values()) {
  if (n <= 40 or n == 100) {
    let ls = leaves(n);
    let bFull = Bitcoin.merkleTree(ls);
    let gFull = Bagged.merkleTree(ls);
    let zFull = ZeroPadded.merkleTree(ls, depth);
    let (bRoot, gRoot, zRoot) = (Reference.bitcoin(ls), Reference.bagged(ls), Reference.padded(ls, depth));
    for (i in Nat.range(0, n)) {
      // Bitcoin
      let bb = bFull.branch(i);
      assert Bitcoin.verifyBranch(ls[i], i, bb, bRoot);
      assert not Bitcoin.verifyBranch(flip(ls[i]), i, bb, bRoot);
      assert not Bitcoin.verifyBranch(ls[i], i, bb, flip(bRoot));
      if (n > 1) {
        // another position of the same depth fails, unless the node there is the same one
        let j = if (i % 2 == 0) i + 1 else (i - 1 : Nat);
        if (j < n) assert not Bitcoin.verifyBranch(ls[i], j, bb, bRoot);
        assert not Bitcoin.verifyBranch(ls[i], i, slice(bb, 1, bb.size()), bRoot);
      };

      // zero-padded
      let zb = zFull.branch(i);
      assert zb.size() == depth and ZeroPadded.verifyBranch(ls[i], i, zb, zRoot);
      assert not ZeroPadded.verifyBranch(flip(ls[i]), i, zb, zRoot);
      assert not ZeroPadded.verifyBranch(ls[i], i + 1, zb, zRoot);

      // bagged
      let gp = gFull.branch(i);
      assert Bagged.verifyInclusion(ls[i], i, n, gp, gRoot);
      assert not Bagged.verifyInclusion(flip(ls[i]), i, n, gp, gRoot);
      assert not Bagged.verifyInclusion(ls[i], i, n, gp.concat([leaf(999)]), gRoot);
      if (gp.size() > 0) assert not Bagged.verifyInclusion(ls[i], i, n, slice(gp, 1, gp.size()), gRoot);
      assert not Bagged.verifyInclusion(ls[i], n, n, gp, gRoot);
    };
    // Malformed proofs give false, they do not trap.
    assert not Bitcoin.verifyBranch(ls[0], 0, [("short" : Blob)], bRoot);
    assert not ZeroPadded.verifyBranch(("short" : Blob), 0, [], zRoot);
    assert not Bagged.verifyInclusion(ls[0], 0, n, [("short" : Blob)], gRoot);
  };
};

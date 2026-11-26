// @testmode wasi
// Proofs: closing a prefix of a tree with the peaks to its right, and the
// inclusion proofs of all three formats, accepting and rejecting.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Prove "../../src/Prove";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Hasher "mo:sha2/Hasher/Sha256";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaf; leaves; slice; flip } = Fixtures;

let sizes : [Nat] = Array.tabulate<Nat>(40, func(i) = i + 1).concat([63, 64, 65, 100, 257]);
let depth = 9;
let padFill = Ssz.fillOf(depth);

// Closing a prefix with the peaks to its right.
//
// For every prefix of every list, the prover's peaks complete the prefix's
// tree to the root of the whole list, for all three formats. A peak too few,
// a peak too many and a wrong peak all give another root.
for (n in sizes.values()) {
  if (n <= 40) {
    let ls = leaves(n);
    let kinds : [(Bool, Peaks.Fill, [[Blob]], Blob)] = [
      (true, #copy, Bitcoin.levels(ls), Reference.bitcoin(ls)),
      (false, #skip, Bagged.levels(ls), Reference.bagged(ls)),
      (false, padFill, Ssz.levels(ls, depth), Reference.padded(ls, depth)),
    ];
    for ((double, fill, levels, root) in kinds.values()) {
      // the empty prefix is the whole root, the whole list needs no peaks
      assert Prove.rightPeaks(levels, 0) == [root] and Prove.rightPeaks(levels, n) == [];
      let t = Peaks.new(2 ** depth, double);
      for (m in Nat.range(1, n + 1)) {
        Peaks.add(t, ls[m - 1]);
        let proof = Prove.rightPeaks(levels, m);
        assert Peaks.close(t, proof, fill, false) and Peaks.spare(t).readSum() == root;
        if (proof.size() > 0) {
          ignore Peaks.close(t, slice(proof, 1, proof.size()), fill, false);
          assert Peaks.spare(t).readSum() != root;
          ignore Peaks.close(t, Fixtures.flipFirst(proof), fill, false);
          assert Peaks.spare(t).readSum() != root;
        };
        ignore Peaks.close(t, proof.concat([leaf(999)]), fill, false);
        assert Peaks.spare(t).readSum() != root;
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
    let bLevels = Bitcoin.levels(ls);
    let gLevels = Bagged.levels(ls);
    let zLevels = Ssz.levels(ls, depth);
    let (bRoot, gRoot, zRoot) = (Reference.bitcoin(ls), Reference.bagged(ls), Reference.padded(ls, depth));
    for (i in Nat.range(0, n)) {
      // Bitcoin
      let bb = Prove.branch(bLevels, i, #copy);
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
      let zb = Prove.branch(zLevels, i, padFill);
      assert zb.size() == depth and Ssz.verifyBranch(ls[i], i, zb, zRoot);
      assert not Ssz.verifyBranch(flip(ls[i]), i, zb, zRoot);
      assert not Ssz.verifyBranch(ls[i], i + 1, zb, zRoot);

      // bagged
      let gp = Prove.branch(gLevels, i, #skip);
      assert Bagged.verifyInclusion(ls[i], i, n, gp, gRoot);
      assert not Bagged.verifyInclusion(flip(ls[i]), i, n, gp, gRoot);
      assert not Bagged.verifyInclusion(ls[i], i, n, gp.concat([leaf(999)]), gRoot);
      if (gp.size() > 0) assert not Bagged.verifyInclusion(ls[i], i, n, slice(gp, 1, gp.size()), gRoot);
      assert not Bagged.verifyInclusion(ls[i], n, n, gp, gRoot);
    };
    // Malformed proofs give false, they do not trap.
    assert not Bitcoin.verifyBranch(ls[0], 0, [("short" : Blob)], bRoot);
    assert not Ssz.verifyBranch(("short" : Blob), 0, [], zRoot);
    assert not Bagged.verifyInclusion(ls[0], 0, n, [("short" : Blob)], gRoot);
  };
};

import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Random "mo:core/Random";
import Bench "mo:bench-helper";
import Bitcoin "../src/Bitcoin";
import Bagged "../src/Bagged";
import Chunks "../src/Chunks";
import Peaks "../src/Peaks";
import Prove "../src/Prove";
import Ssz "../src/Ssz";

module {
  // The cost of a Merkle root over n random 32-byte leaves, for the three
  // kinds of tree and the ways of adding, and of verifying the same leaves in
  // three chunks. The leaves, the trees and the proofs are made at init,
  // outside the measurement; every cell runs once on a tree of its own.
  //
  // A single-SHA node costs two SHA-256 compressions, a double-SHA node
  // three, and a tree over n leaves has about n nodes, so every row is linear
  // in n.

  public func init() : Bench.V1 {
    let counts : [Nat] = [1_000, 8_000];
    let rows = [
      "Bitcoin: add, then root",
      "Bitcoin: addChecked, then root",
      "Bitcoin: merkleRoot (in pairs)",
      "bagged: add, then root",
      "bagged: merkleRoot (in pairs)",
      "zero-padded, depth 20: add, then root",
      "Bitcoin: verify in 3 chunks",
      "bagged: verify in 3 chunks",
    ];
    let cols = counts.map<Nat, Text>(func(n) = n.toText() # " leaves");
    let schema : Bench.Schema = {
      name = "Merkle roots and chunked verification";
      description = "Instructions for a root over n random 32-byte leaves, and for verifying them in three chunks against the root.";
      rows;
      cols;
    };

    let rng : Random.Random = Random.seed(0x6d6d_725f_6265_6e63);
    func leaf() : Blob = (Array.tabulate<Nat8>(32, func(_) = rng.nat8())).toBlob();
    let leaves = counts.map<Nat, [Blob]>(func(n) = Array.tabulate<Blob>(n, func(_) = leaf()));

    // The chunks and their proofs, for the two verifier rows.
    type Plan = {
      chunks : [[Blob]];
      proofs : [[Blob]];
      verifier : Chunks.Verifier;
    };
    func plan(ls : [Blob], levels : [[Blob]], verifier : Chunks.Verifier) : Plan {
      let n = ls.size();
      let bounds : [Nat] = [0, n / 3, 2 * n / 3, n];
      {
        chunks = Array.tabulate<[Blob]>(3, func(c) = Array.tabulate<Blob>(bounds[c + 1] - bounds[c], func(j) = ls[bounds[c] + j]));
        proofs = Array.tabulate<[Blob]>(3, func(c) = Prove.rightPeaks(levels, bounds[c + 1]));
        verifier;
      };
    };
    let bitcoinPlans = leaves.map<[Blob], Plan>(
      func(ls) {
        let levels = Bitcoin.levels(ls);
        plan(ls, levels, Bitcoin.verifier(Prove.root(levels), 13));
      }
    );
    let baggedPlans = leaves.map<[Blob], Plan>(
      func(ls) {
        let levels = Bagged.levels(ls);
        plan(ls, levels, Bagged.verifier(Prove.root(levels), 13));
      }
    );

    // A tree of its own for every cell that builds one.
    let bitcoinTrees = Array.tabulate<[Bitcoin.Tree]>(2, func(_) = counts.map<Nat, Bitcoin.Tree>(Bitcoin.new));
    let baggedTrees = counts.map<Nat, Bagged.Tree>(Bagged.new);
    let paddedTrees = counts.map<Nat, Ssz.Tree>(func(_) = Ssz.new(20));

    // Every way gives the same root.
    for (ls in leaves.values()) {
      let t = Peaks.new(ls.size(), true);
      for (l in ls.values()) t.add(l);
      assert t.root(#copy) == Bitcoin.merkleRoot(ls);
    };

    Bench.V1(
      schema,
      func(ri : Nat, ci : Nat) {
        let ls = leaves[ci];
        switch ri {
          case 0 {
            let t = bitcoinTrees[0][ci];
            for (l in ls.values()) t.add(l);
            ignore t.root();
          };
          case 1 {
            let t = bitcoinTrees[1][ci];
            for (l in ls.values()) assert t.addChecked(l);
            ignore t.root();
          };
          case 2 ignore Bitcoin.merkleRoot(ls);
          case 3 {
            let t = baggedTrees[ci];
            for (l in ls.values()) t.add(l);
            ignore t.root();
          };
          case 4 ignore Bagged.merkleRoot(ls);
          case 5 {
            let t = paddedTrees[ci];
            for (l in ls.values()) t.add(l);
            ignore t.root();
          };
          case 6 {
            let p = bitcoinPlans[ci];
            var c = 0;
            while (c < 3) {
              assert p.verifier.verifyChunk(p.chunks[c], p.proofs[c]);
              c += 1;
            };
          };
          case _ {
            let p = baggedPlans[ci];
            var c = 0;
            while (c < 3) {
              assert p.verifier.verifyChunk(p.chunks[c], p.proofs[c]);
              c += 1;
            };
          };
        };
      },
    );
  };
};

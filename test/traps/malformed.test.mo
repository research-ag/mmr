// Malformed input that has no sensible result traps instead of giving a
// wrong one: a zero-padded fill deeper than 62 or with too short a table,
// and a leaf of the wrong length in the prover's tree, even where the leaf
// is never combined.
//
// A trap ends a call, so each case runs in a call of its own, and the test
// checks that the call failed.
import Peaks "../../src/Peaks";
import Bagged "../../src/Bagged";
import Bitcoin "../../src/Bitcoin";
import MerkleTree "../../src/MerkleTree";
import ZeroPadded "../../src/ZeroPadded";
import Fixtures "../support/Fixtures";

actor {
  public func depth62() : async Blob {
    let t = Peaks.new(4, false, ZeroPadded.fillOf(62));
    t.add(Fixtures.leaf(0));
    t.root();
  };

  public func depth63() : async Blob {
    let t = Peaks.new(4, false, ZeroPadded.fillOf(63));
    t.add(Fixtures.leaf(0));
    t.root();
  };

  public func shortTable() : async () {
    ignore Peaks.withDepth(4, false, #zeros({ table = Peaks.zeros(3, false); depth = 4 }));
  };

  // A record made by hand, past the checks of `new` and `withDepth`.
  public func handMade63() : async Blob {
    let ok = Peaks.withDepth(2, false, #skip);
    let t : Peaks.Tree = {
      hasher = ok.hasher;
      double = false;
      fill = ZeroPadded.fillOf(63);
      var count = 0;
    };
    t.add(Fixtures.leaf(0));
    t.root();
  };

  public func shortSingleLeaf() : async Blob {
    Bagged.merkleTree([("abc" : Blob)]).root();
  };

  public func shortLastLeaf() : async Blob {
    Bitcoin.merkleTree([Fixtures.leaf(0), Fixtures.leaf(1), ("abc" : Blob)]).root();
  };

  public func runTests() : async () {
    // depth 62 is the deepest there is
    ignore await depth62();

    for (bad in [depth63, handMade63, shortSingleLeaf, shortLastLeaf].values()) {
      let trapped = try { ignore await bad(); false } catch (_) { true };
      assert trapped;
    };
    let trapped = try { await shortTable(); false } catch (_) { true };
    assert trapped;
  };
};

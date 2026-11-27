// A zero-padded tree of depth d has 2^d places. With more chunks than that
// it has no root: taking one traps, in the tree and in the whole tree of
// the prover, instead of giving the root of a deeper tree.
//
// A trap ends a call, so each case runs in a call of its own, and the test
// checks that the call failed.
import ZeroPadded "../../src/ZeroPadded";
import Peaks "../../src/Peaks";
import MerkleTree "../../src/MerkleTree";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

persistent actor {
  let depth = 2;

  public func rootOfFull() : async Blob {
    let t = ZeroPadded.new(depth);
    for (l in Fixtures.leaves(4).values()) t.add(l);
    t.root();
  };

  public func rootOfOverfull() : async Blob {
    let t = ZeroPadded.new(depth);
    for (l in Fixtures.leaves(5).values()) t.add(l);
    t.root();
  };

  public func rootWithLengthOfOverfull() : async Blob {
    let t = ZeroPadded.new(depth);
    for (l in Fixtures.leaves(5).values()) t.add(l);
    t.rootWithLength();
  };

  public func loadedOverfull() : async Blob {
    let source = ZeroPadded.new(depth + 1);
    for (l in Fixtures.leaves(5).values()) source.add(l);
    let t = ZeroPadded.new(depth);
    assert t.load(source.count, source.toBlobs());
    t.root();
  };

  public func merkleTreeOfOverfull() : async Blob {
    ZeroPadded.merkleTree(Fixtures.leaves(5), depth).root();
  };

  public func runTests() : async () {
    // all 2^depth places used: a root of that depth
    assert (await rootOfFull()) == Reference.padded(Fixtures.leaves(4), depth);
    assert ZeroPadded.merkleTree(Fixtures.leaves(4), depth).root() == Reference.padded(Fixtures.leaves(4), depth);

    // one chunk more: no root
    for (overfull in [rootOfOverfull, rootWithLengthOfOverfull, loadedOverfull, merkleTreeOfOverfull].values()) {
      let trapped = try { ignore await overfull(); false } catch (_) { true };
      assert trapped;
    };
  };
};

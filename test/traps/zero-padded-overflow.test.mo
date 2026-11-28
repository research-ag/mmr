// A zero-padded tree of depth d has 2^d places. With more chunks than that
// it has no root: taking one traps, in the tree and in the whole tree of
// the prover, instead of giving the root of a deeper tree. Loading more
// peaks than that is refused. And peaks are only copied between trees of
// the same rules.
//
// A trap ends a call, so each case runs in a call of its own, and the test
// checks that the call failed.
import ZeroPadded "../../src/ZeroPadded";
import Peaks "../../src/Peaks";
import MerkleTree "../../src/MerkleTree";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

actor {
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

  public func copyAcrossRules() : async Blob {
    let from = ZeroPadded.new(depth);
    for (l in Fixtures.leaves(3).values()) from.add(l);
    let to = ZeroPadded.new(depth + 1); // same slots would do, but not the same depth
    Peaks.copy(from, to);
    to.root();
  };

  public func merkleTreeOfOverfull() : async Blob {
    ZeroPadded.merkleTree(Fixtures.leaves(5), depth).root();
  };

  public func runTests() : async () {
    // all 2^depth places used: a root of that depth
    assert (await rootOfFull()) == Reference.padded(Fixtures.leaves(4), depth);
    assert ZeroPadded.merkleTree(Fixtures.leaves(4), depth).root() == Reference.padded(Fixtures.leaves(4), depth);

    // one chunk more: no root
    for (overfull in [rootOfOverfull, rootWithLengthOfOverfull, merkleTreeOfOverfull].values()) {
      let trapped = try { ignore await overfull(); false } catch (_) { true };
      assert trapped;
    };

    // loading one peak more than the places is refused, without a trap
    let source = ZeroPadded.new(depth + 1);
    for (l in Fixtures.leaves(5).values()) source.add(l);
    assert not ZeroPadded.new(depth).load(source.count, source.toBlobs());

    // copying between depths traps
    let copied = try { ignore await copyAcrossRules(); false } catch (_) { true };
    assert copied;
  };
};

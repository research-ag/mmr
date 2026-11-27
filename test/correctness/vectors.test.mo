// @testmode wasi
// The roots of the package against the references of `Reference`: over
// generated leaves, and for the zero hashes of SSZ.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import ZeroPadded "../../src/ZeroPadded";
import Nat "mo:core/Nat";
import Fixtures "../support/Fixtures";
import Reference "../support/Reference";

let { leaves } = Fixtures;

// Roots against the references.
//
// For each number of leaves n, over the leaves SHA256("leaf0"),
// SHA256("leaf1"), ..., the Bitcoin root, the bagged root, the zero-padded
// root at depth 7 and the same with the length mixed in are compared with
// those of `Reference`. The sizes cover the powers of two and their
// neighbours, where the carries of the tree are longest.
do {
  let sizes : [Nat] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 16, 17, 31, 32, 33, 100];
  for (n in sizes.values()) {
    let ls = leaves(n);
    let padded = Reference.padded(ls, 7);
    let withLength = Reference.withLength(padded, n);
    assert Bitcoin.merkleRoot(ls) == Reference.bitcoin(ls);
    assert Bagged.merkleRoot(ls) == Reference.bagged(ls);
    assert ZeroPadded.merkleize(ls, ?128) == padded;
    // the same roots from a tree that is filled leaf by leaf
    let t = ZeroPadded.new(7);
    for (l in ls.values()) t.add(l);
    assert t.root() == padded and t.rootWithLength() == withLength;
    assert ZeroPadded.mixInLength(padded, n) == withLength;
  };
};

// The zero hashes of SSZ, and the empty deposit tree.
//
// Zero hash k is the root of a tree of depth k that holds no leaf: the 32
// zero bytes for k = 0, and zero hash k - 1 combined with itself above. All
// of them, up to depth 32 as in the Ethereum deposit contract, are compared
// with the reference, and so are the roots of the empty deposit tree.
do {
  let z = Peaks.zeros(32, false);
  assert z.size() == 33;
  var expected = Reference.padded([], 0);
  for (k in Nat.range(0, 33)) {
    assert z[k] == expected;
    expected := Reference.sha(expected, expected);
  };
  let deposits = ZeroPadded.new(32);
  assert deposits.root() == z[32];
  assert deposits.rootWithLength() == Reference.withLength(z[32], 0);
  assert ZeroPadded.merkleize([], null) == z[0];
};

// Straightforward reference implementations of the three tree formats. They
// use only the plain `Sha256` digest and build every level of the tree in
// full, so that they share no code and no idea of "peaks" with the package:
// the package is correct when it agrees with them.
import Array "mo:core/Array";
import Blob "mo:core/Blob";
import Nat "mo:core/Nat";
import Sha256 "mo:sha2/Sha256";
import Fixtures "Fixtures";

module {
  // The 32 zero bytes: the zero-padded tree's node for a place that holds
  // no leaf.
  let zero : Blob = "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00";

  // A node from its two children: SHA-256 of the 64 bytes left ++ right.
  public func sha(l : Blob, r : Blob) : Blob {
    let d = Sha256.new();
    d.writeBlob(l);
    d.writeBlob(r);
    d.sum();
  };

  // A node from its two children, the Bitcoin way: SHA-256 applied twice.
  public func dsha(l : Blob, r : Blob) : Blob {
    let d = Sha256.new();
    d.writeBlob(l);
    d.writeBlob(r);
    d.sumDouble();
  };

  // The Bitcoin root, computed level by level. The last node of a level of
  // odd length is paired with itself.
  public func bitcoin(ls : [Blob]) : Blob {
    var level = ls;
    while (level.size() > 1) {
      let below = level;
      let m = below.size();
      level := Array.tabulate<Blob>((m + 1) / 2, func(i) = dsha(below[2 * i], if (2 * i + 1 < m) below[2 * i + 1] else below[2 * i]));
    };
    level[0];
  };

  // The bagged root, from the recursive definition of RFC 6962 without its
  // prefixes: the left subtree is the largest power of two below n leaves.
  public func bagged(ls : [Blob]) : Blob {
    let n = ls.size();
    if (n == 1) return ls[0];
    var k = 1;
    while (k * 2 < n) k *= 2;
    sha(bagged(Fixtures.slice(ls, 0, k)), bagged(Fixtures.slice(ls, k, n)));
  };

  // The zero-padded root: all 2^depth places written out, the missing ones
  // as zeros, and then combined level by level.
  public func padded(ls : [Blob], depth : Nat) : Blob {
    var level = Array.tabulate<Blob>(2 ** depth, func(i) = if (i < ls.size()) ls[i] else zero);
    while (level.size() > 1) {
      let below = level;
      level := Array.tabulate<Blob>(below.size() / 2, func(i) = sha(below[2 * i], below[2 * i + 1]));
    };
    level[0];
  };

  // SSZ's `mix_in_length`: the root and the length combined like two
  // children, the length as a 32-byte little-endian number.
  public func withLength(root : Blob, length : Nat) : Blob {
    let chunk = Array.tabulate<Nat8>(32, func(i) = if (i < 8) ((length / 256 ** i) % 256).toNat8() else 0);
    sha(root, chunk.toBlob());
  };
};

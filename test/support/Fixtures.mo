// Test data shared by the test files: deterministic leaves and the small
// helpers that build lists, chunks and corrupted copies of them.
import Array "mo:core/Array";
import Blob "mo:core/Blob";
import List "mo:core/List";
import Nat "mo:core/Nat";
import Text "mo:core/Text";
import Sha256 "mo:sha2/Sha256";

module {
  // The i-th leaf: SHA256("leaf<i>"). The test vectors of an independent
  // implementation are computed over these same leaves.
  public func leaf(i : Nat) : Blob = Sha256.fromBlob(("leaf" # i.toText()).encodeUtf8());

  // The first n leaves: leaf(0), leaf(1), ..., leaf(n - 1).
  public func leaves(n : Nat) : [Blob] = Array.tabulate<Blob>(n, leaf);

  // The elements of `a` from index `from` (inclusive) to `to` (exclusive).
  public func slice(a : [Blob], from : Nat, to : Nat) : [Blob] = Array.tabulate<Blob>(to - from, func(i) = a[from + i]);

  // The same hash with one bit changed, so that it is a valid-looking hash
  // that belongs to no tree.
  public func flip(b : Blob) : Blob {
    let a = b.toArray();
    Array.tabulate<Nat8>(a.size(), func(i) = if (i == 5) a[5] ^ 0x01 else a[i]).toBlob();
  };

  // The list with its first element flipped. Used to forge a chunk or a
  // proof whose length and shape are right.
  public func flipFirst(a : [Blob]) : [Blob] = Array.tabulate<Blob>(a.size(), func(i) = if (i == 0) flip(a[0]) else a[i]);

  // The smallest depth d with 2^d >= n: the depth of the smallest perfect
  // tree that holds n leaves.
  public func depthFor(n : Nat) : Nat {
    var d = 0;
    while (2 ** d < n) d += 1;
    d;
  };

  // The end points of a sequence of chunks that covers n leaves, each chunk
  // starting where the previous one ended. The chunk lengths start at
  // `step` and then vary in a fixed pseudo-random way, so that the chunks
  // start at both odd and even positions. A `step` of at least n gives one
  // chunk with everything.
  public func chunkEnds(n : Nat, step : Nat) : [Nat] {
    let ends = List.empty<Nat>();
    var from = 0;
    var length = step;
    while (from < n) {
      let to = if (from + length >= n) n else from + length;
      length := 1 + (length * 7 + from) % (2 * step);
      ends.add(to);
      from := to;
    };
    ends.toArray();
  };
};

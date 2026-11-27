// The measuring tools of the allocation tests, and the units that the
// expected sizes are written in.
//
// `Prim.rts_total_allocation()` counts all bytes ever allocated, so its
// difference around a piece of code is what that code allocated. The counter
// is maintained only in compiled wasm, hence the wasi test mode of the files
// that import this module.
import Hasher "mo:sha2/Hasher/Sha256";
import Nat "mo:core/Nat";
import Peaks "../../src/Peaks";
import Prim "mo:prim";

module {
  // The number of bytes that `f` allocates.
  public func alloc(f : () -> ()) : Nat {
    let before = Prim.rts_total_allocation();
    f();
    Prim.rts_total_allocation() - before;
  };

  // Fails the test, and says which measurement, if `actual` differs from
  // `expected`.
  public func check(name : Text, actual : Nat, expected : Nat) {
    if (actual != expected) {
      Prim.debugPrint(name # ": allocated " # actual.toText() # " bytes, expected " # expected.toText());
      assert false;
    };
  };

  // The units that the expectations are made of. They are measured, not
  // hard-coded, so that the tests do not depend on the runtime's object
  // layout.
  public type Units = {
    // A root as a `Blob`.
    readout : Nat;
    // One SHA-256 hasher.
    oneHasher : Nat;
    // One slot of an array.
    word : Nat;
    // The smallest tree: `Peaks.withDepth(0, true)`.
    pool0 : Nat;
  };

  // Measures the units, after checking the harness itself: an empty closure
  // allocates nothing.
  public func units() : Units {
    check("harness", alloc(func() {}), 0);
    let probe = Hasher.new();
    let readout = alloc(func() { ignore probe.readSum() });
    let oneHasher = alloc(func() { ignore Hasher.new() });
    let word = alloc(func() { ignore Prim.Array_init<Nat>(2, 0) }) - alloc(func() { ignore Prim.Array_init<Nat>(1, 0) }) : Nat;
    let pool0 = alloc(func() { ignore Peaks.withDepth(0, true) });
    assert readout > 0 and oneHasher > 0;
    { readout; oneHasher; word; pool0 };
  };
};

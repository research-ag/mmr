// @testmode wasi
// The trees, proofs and verifiers of the package against straightforward
// references written here with the plain `Sha256` digest, and against vectors
// computed by an independent implementation in another language.
import Peaks "../src/Peaks";
import Bitcoin "../src/Bitcoin";
import Bagged "../src/Bagged";
import Ssz "../src/Ssz";
import Chunks "../src/Chunks";
import Prove "../src/Prove";
import Hasher "mo:sha2/Hasher/Sha256";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Blob "mo:core/Blob";
import Char "mo:core/Char";
import Nat "mo:core/Nat";
import Nat32 "mo:core/Nat32";
import Nat64 "mo:core/Nat64";
import Runtime "mo:core/Runtime";
import Text "mo:core/Text";

// --- Helpers ---

func leaf(i : Nat) : Blob = Sha256.fromBlob(("leaf" # i.toText()).encodeUtf8());
func leaves(n : Nat) : [Blob] = Array.tabulate<Blob>(n, leaf);
func slice(a : [Blob], from : Nat, to : Nat) : [Blob] = Array.tabulate<Blob>(to - from, func(i) = a[from + i]);
func flip(b : Blob) : Blob {
  let a = b.toArray();
  Array.tabulate<Nat8>(a.size(), func(i) = if (i == 5) a[5] ^ 0x01 else a[i]).toBlob();
};
func hex(t : Text) : Blob {
  func digit(c : Char) : Nat8 {
    let n = c.toNat32();
    if (n >= 48 and n <= 57) return Nat32.toNat8(n - 48);
    if (n >= 97 and n <= 102) return Nat32.toNat8(n - 87);
    Runtime.trap("bad hex digit");
  };
  let chars = t.toArray();
  Array.tabulate<Nat8>(chars.size() / 2, func(i) = digit(chars[2 * i]) << 4 | digit(chars[2 * i + 1])).toBlob();
};

// --- References ---

func sha(l : Blob, r : Blob) : Blob {
  let d = Sha256.new();
  d.writeBlob(l);
  d.writeBlob(r);
  d.sum();
};
func dsha(l : Blob, r : Blob) : Blob {
  let d = Sha256.new();
  d.writeBlob(l);
  d.writeBlob(r);
  d.sumDouble();
};
// Bitcoin: level by level, the last node of an odd level paired with itself.
func refBitcoin(ls : [Blob]) : Blob {
  var level = ls;
  while (level.size() > 1) {
    let below = level;
    let m = below.size();
    level := Array.tabulate<Blob>((m + 1) / 2, func(i) = dsha(below[2 * i], if (2 * i + 1 < m) below[2 * i + 1] else below[2 * i]));
  };
  level[0];
};
// Bagged: the recursive definition of RFC 6962, without the prefixes.
func refBagged(ls : [Blob]) : Blob {
  let n = ls.size();
  if (n == 1) return ls[0];
  var k = 1;
  while (k * 2 < n) k *= 2;
  sha(refBagged(slice(ls, 0, k)), refBagged(slice(ls, k, n)));
};
// Zero-padded: all 2^depth places written out, level by level.
func refPadded(ls : [Blob], depth : Nat) : Blob {
  let zero : Blob = "\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00";
  var level = Array.tabulate<Blob>(2 ** depth, func(i) = if (i < ls.size()) ls[i] else zero);
  while (level.size() > 1) {
    let below = level;
    level := Array.tabulate<Blob>(below.size() / 2, func(i) = sha(below[2 * i], below[2 * i + 1]));
  };
  level[0];
};

let sizes : [Nat] = Array.tabulate<Nat>(40, func(i) = i + 1).concat([63, 64, 65, 100, 257]);
let depth = 9; // of the zero-padded trees below: 512 places
let padFill = Ssz.fillOf(depth);

// --- Vectors from an independent implementation ---
// (n, Bitcoin root, bagged root, zero-padded root at depth 7, the same with the length mixed in)
// over the leaves SHA256("leaf0"), SHA256("leaf1"), ...
do {
  let vectors : [(Nat, Text, Text, Text, Text)] = [
    (1, "4d5a9584d985e8fb44015a8affa9b76f1ff16f65e61df7156d8e8159e1448978", "4d5a9584d985e8fb44015a8affa9b76f1ff16f65e61df7156d8e8159e1448978", "0e5a60226264d543901393856551cc9bc8ee371fc33fc66b8c27eee79bdf57fb", "4b2dad05cf8ac4d95785c9af2fbbeb33e217ae9bff6fba6c8b19371c49fa76a9"),
    (2, "88ae06d4e79d7a574f4eeba5a8285cc6f7b9e1905710e548d59ef24a684dcf42", "884ff14f19d1564614ab3184d7bdc35a1a9ff90d36ac962b05a81aeb56027c22", "40fd17a4362e7df0cc88cd16929ed9528a80a8862c0521cdeb2d7efabec9f5da", "fb8b8ea312068e867d098fde66ecee5e8207b2f621c600adcd4aa0d20c789c7d"),
    (3, "a1fe7f5def45dc1aba0cdfe3ff51f1e80ba3db1a2b2ef2b047cf617b471be10a", "bbd487c8ef68d4609e769c175187e0b8aaa9caf8fd47b03fae7a6f928eb53e2c", "af21ab6d5b8e6932d0d9aa3fd631341ebd851b87284434a0eeebdfaef62e1f00", "40d0a7fa8f51badfd816e82d053d091b79bc3dab35e5c7dd574115592a0b6ab8"),
    (4, "d06f1c79983679fa6e4b90605400016088eaba4f73d0a97dc5a4eebb39e1df80", "8910150e02a7fe57232749c31f7cfd48a8439011e34227c6b7e3eb7d98440ee6", "6a21bd735f6b4973942b876540a1c37f0dfd30cc705575033bf9a7378b142c90", "27cd3be853f57f0a6d1af5c0c54ae8c2b3e8b77fc6dc47e9f61fc58117efddcc"),
    (5, "01005137f4b7eab2891fa19bcd3fb0a370c7c34968a79626bb26076225804cb0", "97be122a06123ea27a51dfff3abdc6f7c6345b924ed78926c4b5dadc9be689d5", "0ca65b9971ec699c87b478dfd5383f53105a3d6686028014dca11e9a682d669c", "ec1c797ca7b4e019774f72465cf2b68b41bc0d16fa3ec53fc66432a8827aafc0"),
    (6, "e692fff1f894fd2bc906a1827b2acf87b234edddd469ab4a1d11b1173c969976", "83827d1930084043aa2c13b28fd9343c6800b0ba8dbd0930cd6f8a09d68ace8a", "00f74cdc83b8e41c2df4a14f982ea1e1887752aed99eee3c33db6005883675c7", "0d028e094e0cbf3dabdb8e9132644157f58770c0113776694345f6a9f1523fd8"),
    (7, "c7522c347b71927d72b3cb6b61e80df48f2ebc12eeb20a0cc6b2fdedbff7a654", "2ac7825c69a32b24c921fcb43bdc7044467d222c89a6c626712f745a71128496", "bd910ab6654862e2bdce3732d555bc78d5addd6b219ad7fb0d2bb425eeb7b22b", "bc3991810e108a0d74f6a5e8e61016f3343a6ac9a3085f096b966c8d7be0392e"),
    (8, "0e128ed8acd3e851e7c8b117c4726144f3b54c89b08012ae58ad1c89b25ea164", "c2a49b5199fe03d9bc8fbbdaa10ed43f9a657dabacfe18caadbe63207843d015", "2694e75c81505677a5dd4d05521cec2d72ed82b378b62a1087769527919b47d5", "c90cb63a78cfff8dccdb17dc6f8d6f645d0720455b15003295e654da49d1ef3d"),
    (9, "d80bcc01cb7005a0078ba92e6ae7c10961a0113e9c2160eb2f27e94d3d19a4e0", "51a67810ed2ef5aaa096920f60078e35d102aeef1ca206b5320775f0c2535cd2", "6f03ead80f29b89c9037297c8a806a757110b8594fac3eeadb62cc9dee3065aa", "26d30bc0c97bd80f88883ec133234ef2a748bc07cc93761196a77a9e2c8d6e2d"),
    (13, "b9bbe304255cf2b992384206073fbfd395e65cbbb2be8cf8fde7d282d5d1c9cc", "248df2e412117182517f6df8a33fb0d2f3cdf15de6b50c9c45a5f0d53a1410d8", "85c4dfd2885bc0fd181b93151386ad10d48af556225cb5fe358b20c5750b1be1", "635320d96622c147037d4f36c7b310ef3238f530de6a9bd65fa8c87025aa7e56"),
    (16, "0efc8aae5b329e3bc8c18b2ebca5ff23c98af3d34c1b648d5faefc70af3988b2", "d3893bcd4516a784d8ab534095d8036297cccf2bcebb8c62ef2d530f6560c5ef", "84bc554585344d8b18a95bab2a07bc8c48dd3ee1a3c73b4ecf989025f51cd756", "a77461b30c50d8ac40980a391b485f4745472125e64da73c197afb2fb3deb054"),
    (17, "c4378889612d307a4a9c63d34e7b3bba5d8e730aeb154f1e284ee8cda1edd20c", "d9a7bd11d11ae8d967983944e178423d5cfd285936d469a18367da4c0de0c492", "64aa94f50a73abfca276fe69dfdfa571a1140b567123579db5e0890986f64b7c", "919b7b8eb30d2e7cf1f85fb8d9731866b410271a67219fc4065ae47107541948"),
    (31, "76995a8f242176573cc58069bca75b205186ae662d8538417dc898133091d99a", "acf7448b657f2a9096f8576dffb17fbc296ace36ce4d293da317bb3e41136b52", "bd10f9841765c3b61fdb1545d063abc18fd93126aecab278bc85fe7127bedf07", "6bcf4d5816d5399abc59bb5c28cf72448f26d6b728732ce49057334e055d6947"),
    (32, "436996c6000e36ce60c50b02928d7952a65425ac6e3fb2cb632201595f2bd3d4", "09105d8b10ab40e7fc2aa9582e16eb45304733e03e08ad75f3e9739cedde2e67", "b0c4db0fe819255ab7eac3757cdf7d96cc4ee45e7f403dca97fa4249e000951e", "25032904c3272392d1ddc042698d9980ffde0dc707e4de6a53fbab3d2f758ac3"),
    (33, "6e1e2a6e3ddb591e0e107a265623581fc504ee903ebc787645163cecebbf0c2c", "5a686db939d5f4d73c7c01200a773d98b171f6000b37dd34e8d7a88f8928d872", "ca2e7c180f985dc4b5e5f392ef3540fe49db9dc1d8b4630357b11f7c4451fb68", "42e65a8c85f0563f1e39ad5a4f4d3aa7a217d13fea06d44c7ea86d040e138dca"),
    (100, "71c214c59d04662e9128de111d83cf98e25df3f8cc34d57006edea5f141f118b", "d38e4e72eddcbf9614287f19084c8f14caacad964ba27b9279899415600f2bdc", "3a43dd62356c2b77367f6204123894528647c2a1296a7cdacfea33de4c995839", "2402646e740973338298e4dacb2a0aebbbfc1d68f71132bf05c3cc28112ab575"),
  ];
  assert leaf(0) == hex("4d5a9584d985e8fb44015a8affa9b76f1ff16f65e61df7156d8e8159e1448978");
  for ((n, bitcoin, bagged, padded, withLength) in vectors.values()) {
    let ls = leaves(n);
    assert Bitcoin.merkleRoot(ls) == hex(bitcoin);
    assert Bagged.merkleRoot(ls) == hex(bagged);
    assert Ssz.merkleize(ls, ?128) == hex(padded);
    let t = Ssz.new(7);
    for (l in ls.values()) Ssz.add(t, l);
    assert Ssz.root(t) == hex(padded) and Ssz.rootWithLength(t) == hex(withLength);
    assert Ssz.mixInLength(hex(padded), n) == hex(withLength);
  };
};

// --- Known constants ---
do {
  // SSZ: the first zero hashes, and the root of the empty deposit tree.
  let z = Peaks.zeros(32, false);
  assert z.size() == 33 and z[0].size() == 32;
  assert z[1] == hex("f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b");
  assert z[2] == hex("db56114e00fdd4c1f85c892bf35ac9a89289aaecb1ebd0a96cde606a748b5d71");
  let deposits = Ssz.new(32);
  assert Ssz.root(deposits) == z[32];
  assert Ssz.rootWithLength(deposits) == hex("d70a234731285c6804c2a4f56711ddb8c82c99740f207854891028af34e27e5e");
  assert Ssz.merkleize([], null) == z[0];

  // Bitcoin mainnet: block 170 (2 transactions) and block 586 (3, so the
  // last node is duplicated). Txids and roots in internal byte order: the
  // display hex reversed.
  func rev(t : Text) : Blob {
    let a = hex(t).toArray();
    Array.tabulate<Nat8>(a.size(), func(i) = a[a.size() - 1 - i]).toBlob();
  };
  assert Bitcoin.merkleRoot([
    rev("b1fea52486ce0c62bb442b530a3f0132b826c74e473d1f2c220bfa78111c5082"),
    rev("f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16"),
  ]) == rev("7dac2c5666815c17a3b36427de37bb9d2e2c5ccec3f8633eb91a4205cb4c10ff");
  assert Bitcoin.merkleRoot([
    rev("d45724bacd1480b0c94d363ebf59f844fb54e60cdfda0cd38ef67154e9d0bc43"),
    rev("4d6edbeb62735d45ff1565385a8b0045f066055c9425e21540ea7a8060f08bf2"),
    rev("6bf363548b08aa8761e278be802a2d84b8e40daefe8150f9af7dd7b65a0de49f"),
  ]) == rev("197b3d968ce463aa5da7d8eeba8af35eba80ded4e4fe6808e6cc0dd1c069594d");
};

// --- Roots against the references, by every way of adding ---
for (n in sizes.values()) {
  let ls = leaves(n);
  let bitcoin = refBitcoin(ls);
  let bagged = refBagged(ls);
  let padded = refPadded(ls, depth);

  // the presets, leaf by leaf, with a root after every leaf
  let b = Bitcoin.new(n);
  let g = Bagged.new(n);
  let z = Ssz.new(depth);
  for (i in Nat.range(0, n)) {
    Bitcoin.add(b, ls[i]);
    Bagged.add(g, ls[i]);
    Ssz.add(z, ls[i]);
    if (n <= 40) {
      let prefix = slice(ls, 0, i + 1);
      assert Bitcoin.root(b) == refBitcoin(prefix) and Bagged.root(g) == refBagged(prefix) and Ssz.root(z) == refPadded(prefix, depth);
    };
  };
  assert Bitcoin.root(b) == bitcoin and Bagged.root(g) == bagged and Ssz.root(z) == padded;
  assert Bitcoin.root(b) == bitcoin; // taking a root changes nothing
  assert Bitcoin.count(b) == n.toNat64() and Bagged.count(g) == n.toNat64() and Ssz.count(z) == n.toNat64();

  // one shot, in pairs
  assert Bitcoin.merkleRoot(ls) == bitcoin and Bagged.merkleRoot(ls) == bagged and Ssz.merkleize(ls, ?(2 ** depth)) == padded;

  // smallest depth: padded to the next power of two
  var small = 0;
  while (2 ** small < n) small += 1;
  assert Ssz.merkleize(ls, null) == refPadded(ls, small);
  assert Peaks.root(g.peaks, #zeros({ table = Peaks.zeros(small, false); depth = null })) == refPadded(ls, small);

  // the prover's levels have the same roots
  assert Prove.root(Bitcoin.levels(ls)) == bitcoin and Prove.root(Bagged.levels(ls)) == bagged and Prove.root(Ssz.levels(ls, depth)) == padded;

  // leaves from hashers, and from messages through a digest
  let s = Peaks.new(n, true);
  let h = Hasher.new();
  for (l in ls.values()) { h.loadBlob32(l); Peaks.addState(s, h) };
  assert Peaks.root(s, #copy) == bitcoin;
  let d = Sha256.new();
  let single = Peaks.new(n, false);
  let double = Peaks.new(n, true);
  for (i in Nat.range(0, n)) {
    let message = ("leaf" # i.toText()).encodeUtf8();
    Peaks.addMessage(single, d, message);
    Peaks.addMessage(double, d, message);
  };
  assert Peaks.root(single, #skip) == bagged;
  assert Peaks.root(double, #copy) == refBitcoin(Array.tabulate<Blob>(n, func(i) = Sha256.fromBlob(ls[i])));
};

// --- addAll: a run of leaves, in pairs, starting from any count ---
// Split anywhere into three runs, the peaks are those of adding leaf by leaf.
for (n in ([1, 2, 3, 4, 5, 8, 9, 16, 17, 33] : [Nat]).values()) {
  let ls = leaves(n);
  let one = Peaks.new(n, true);
  for (l in ls.values()) one.add(l);
  let peaks = one.toBlobs();
  for (cut in Nat.range(0, n + 1)) {
    for (cut2 in ([cut, (cut + n) / 2, n] : [Nat]).values()) {
      for (checked in [false, true].values()) {
        let t = Peaks.new(n, true);
        assert t.addAll(ls, 0, cut, checked) and t.count == cut.toNat64();
        assert t.addAll(ls, cut, cut2, checked) and t.count == cut2.toNat64();
        assert t.addAll(ls, cut2, n, checked) and t.toBlobs() == peaks;
      };
    };
  };
  // an empty run adds nothing; a run inside the list adds only that run
  let t = Peaks.new(n, false);
  assert t.addAll(ls, n, n, true) and t.count == 0;
  if (n >= 3) {
    assert t.addAll(ls, 1, n - 1 : Nat, false);
    assert t.root(#skip) == refBagged(slice(ls, 1, n - 1 : Nat));
  };
};
// With the check, the verdict is that of adding leaf by leaf, for every list
// of up to 6 leaves over three values and every place to split it.
do {
  let values = leaves(3);
  var lists = 0;
  var refused = 0;
  for (n in Nat.range(1, 7)) {
    for (code in Nat.range(0, 3 ** n)) {
      var c = code;
      let list = Array.tabulate<Blob>(n, func(_) { let v = values[c % 3]; c /= 3; v });
      let one = Peaks.new(8, true);
      var ok = true;
      for (l in list.values()) if (ok and not one.addChecked(l)) ok := false;
      for (cut in Nat.range(0, n)) {
        let t = Peaks.new(8, true);
        assert (t.addAll(list, 0, cut, true) and t.addAll(list, cut, n, true)) == ok;
        if (ok) assert t.toBlobs() == one.toBlobs();
      };
      lists += 1;
      if (not ok) refused += 1;
    };
  };
  assert lists == 1092 and refused > 0 and refused < lists;
};

// --- carry at a height: a tree from the roots of subtrees ---
// Adding the root of every aligned block of 2^k leaves at height k gives the
// same peaks as adding the leaves one by one.
for (n in ([8, 12, 16, 20, 100] : [Nat]).values()) {
  let ls = leaves(n);
  for (k in Nat.range(0, 3)) {
    let width = 2 ** k;
    if (n % width == 0) {
      let t = Peaks.new(n, true);
      for (j in Nat.range(0, n / width)) {
        Peaks.spare(t).loadBlob32(refBitcoin(slice(ls, j * width, (j + 1) * width)));
        Peaks.carry(t, k.toNat64());
      };
      assert t.count == n.toNat64() and Peaks.root(t, #copy) == refBitcoin(ls);
      let u = Bitcoin.new(n);
      for (l in ls.values()) Bitcoin.add(u, l);
      assert Peaks.toBlobs(t) == Peaks.toBlobs(u.peaks);
    };
  };
};

// --- Saving, exporting and restoring ---
for (n in ([1, 2, 3, 7, 8, 21, 100] : [Nat]).values()) {
  let ls = leaves(n);
  let t = Peaks.new(200, true);
  for (l in ls.values()) t.add(l);
  let peaks = t.toBlobs();
  assert peaks.size() == Nat64.bitcountNonZero(n.toNat64()).toNat();
  // copy aside, grow, copy back
  let aside = Peaks.new(200, true);
  Peaks.copy(t, aside);
  t.add(leaf(1000));
  assert t.root(#copy) != aside.root(#copy);
  Peaks.copy(aside, t);
  assert t.count == n.toNat64() and t.root(#copy) == refBitcoin(ls) and t.toBlobs() == peaks;
  // a fresh tree from the exported peaks goes on as the original does
  let u = Peaks.new(200, true);
  assert u.load(n.toNat64(), peaks);
  u.add(leaf(n));
  assert u.root(#copy) == refBitcoin(leaves(n + 1));
  // malformed input is refused and changes nothing
  assert not u.load(n.toNat64() + 1, peaks.concat([leaf(0), leaf(1), leaf(2), leaf(3), leaf(4), leaf(5), leaf(6), leaf(7)]));
  assert not u.load(1000, []);
  assert not u.load(1, [("short" : Blob)]);
  assert u.count == n.toNat64() + 1;
};

// --- Closing a prefix with the peaks to its right ---
// For every prefix of every list: the prover's peaks complete the prefix's
// tree to the root of the whole list, for all three kinds of tree.
for (n in sizes.values()) {
  if (n <= 40) {
    let ls = leaves(n);
    let kinds : [(Bool, Peaks.Fill, [[Blob]], Blob)] = [
      (true, #copy, Bitcoin.levels(ls), refBitcoin(ls)),
      (false, #skip, Bagged.levels(ls), refBagged(ls)),
      (false, padFill, Ssz.levels(ls, depth), refPadded(ls, depth)),
    ];
    for ((double, fill, levels, root) in kinds.values()) {
      assert Prove.rightPeaks(levels, 0) == [root] and Prove.rightPeaks(levels, n) == [];
      let t = Peaks.new(2 ** depth, double);
      for (m in Nat.range(1, n + 1)) {
        Peaks.add(t, ls[m - 1]);
        let proof = Prove.rightPeaks(levels, m);
        assert Peaks.close(t, proof, fill, false) and Peaks.spare(t).readSum() == root;
        // a peak too few, a peak too many, a wrong peak
        if (proof.size() > 0) {
          ignore Peaks.close(t, slice(proof, 1, proof.size()), fill, false);
          assert Peaks.spare(t).readSum() != root;
          ignore Peaks.close(t, Array.tabulate<Blob>(proof.size(), func(i) = if (i == 0) flip(proof[0]) else proof[i]), fill, false);
          assert Peaks.spare(t).readSum() != root;
        };
        ignore Peaks.close(t, proof.concat([leaf(999)]), fill, false);
        assert Peaks.spare(t).readSum() != root;
      };
    };
  };
};

// --- Inclusion proofs ---
for (n in sizes.values()) {
  if (n <= 40 or n == 100) {
    let ls = leaves(n);
    let bLevels = Bitcoin.levels(ls);
    let gLevels = Bagged.levels(ls);
    let zLevels = Ssz.levels(ls, depth);
    let (bRoot, gRoot, zRoot) = (refBitcoin(ls), refBagged(ls), refPadded(ls, depth));
    for (i in Nat.range(0, n)) {
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

      let zb = Prove.branch(zLevels, i, padFill);
      assert zb.size() == depth and Ssz.verifyBranch(ls[i], i, zb, zRoot);
      assert not Ssz.verifyBranch(flip(ls[i]), i, zb, zRoot);
      assert not Ssz.verifyBranch(ls[i], i + 1, zb, zRoot);

      let gp = Prove.branch(gLevels, i, #skip);
      assert Bagged.verifyInclusion(ls[i], i, n, gp, gRoot);
      assert not Bagged.verifyInclusion(flip(ls[i]), i, n, gp, gRoot);
      assert not Bagged.verifyInclusion(ls[i], i, n, gp.concat([leaf(999)]), gRoot);
      if (gp.size() > 0) assert not Bagged.verifyInclusion(ls[i], i, n, slice(gp, 1, gp.size()), gRoot);
      assert not Bagged.verifyInclusion(ls[i], n, n, gp, gRoot);
    };
    // malformed proofs give false, they do not trap
    assert not Bitcoin.verifyBranch(ls[0], 0, [("short" : Blob)], bRoot);
    assert not Ssz.verifyBranch(("short" : Blob), 0, [], zRoot);
    assert not Bagged.verifyInclusion(ls[0], 0, n, [("short" : Blob)], gRoot);
  };
};

// --- The chunk verifier, for all three kinds of tree ---
// Random-looking chunk sequences are accepted chunk by chunk; a forged leaf,
// a dropped or wrong peak, a peak too many, a wrong root and a chunk after
// completion are rejected; and a rejected chunk leaves the verifier as it was
// (these verifiers have a backup).
func battery(ls : [Blob], levels : [[Blob]], root : Blob, make : Blob -> Chunks.Verifier, minimal : Bool) {
  let n = ls.size();
  for (step in ([1, 2, 3, 5, 8, 1000] : [Nat]).values()) {
    let v = make(root);
    var m = 0;
    var s = step;
    while (m < n) {
      let m2 = if (m + s >= n) n else m + s;
      s := 1 + (s * 7 + m) % (2 * step); // vary the chunk length
      let chunk = slice(ls, m, m2);
      let p = Prove.rightPeaks(levels, m2);
      assert not v.verifyChunk(chunk, p.concat([leaf(999)]));
      if (p.size() > 0) {
        assert not v.verifyChunk(chunk, slice(p, 1, p.size()));
        assert not v.verifyChunk(chunk, Array.tabulate<Blob>(p.size(), func(i) = if (i == 0) flip(p[0]) else p[i]));
      };
      assert not v.verifyChunk(Array.tabulate<Blob>(chunk.size(), func(i) = if (i == 0) flip(chunk[0]) else chunk[i]), p);
      assert not v.verifyChunk([], p);
      assert v.count() == m.toNat64();
      assert v.verifyChunk(chunk, p);
      assert v.count() == m2.toNat64();
      if (minimal) assert v.complete() == (m2 == n);
      m := m2;
    };
    assert v.complete();
    assert not v.verifyChunk([ls[0]], []);
  };
  assert not make(flip(root)).verifyChunk(ls, []);
  // malformed input is rejected, not trapped on
  let w = make(root);
  assert not w.verifyChunk(Array.tabulate<Blob>(n, func(i) = if (i == 0) ("short" : Blob) else ls[i]), []);
  assert not w.verifyChunk(ls, [("short" : Blob)]);
  assert w.verifyChunk(ls, []) and w.complete();
};
for (n in ([1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 23, 31, 32, 33, 64, 100, 257] : [Nat]).values()) {
  let ls = leaves(n);
  battery(ls, Bitcoin.levels(ls), refBitcoin(ls), func(r) = Bitcoin.verifier(r, 10), true);
  battery(ls, Bagged.levels(ls), refBagged(ls), func(r) = Bagged.verifier(r, 10), true);
  battery(ls, Ssz.levels(ls, depth), refPadded(ls, depth), func(r) = Ssz.verifier(r, depth), false);

  // more leaves than the verifier has room for are rejected
  var d = 0;
  while (2 ** d < n) d += 1;
  assert Bitcoin.verifier(refBitcoin(ls), d).verifyChunk(ls, []);
  if (d > 0) assert not Bitcoin.verifier(refBitcoin(ls), d - 1 : Nat).verifyChunk(ls, []);
};

// --- The chunk verifier on a caller's tree, without a backup ---
// One tree per kind serves every verifier below, one after another, whatever
// the one before left in it. Honest chunks are accepted as with a backup. A
// chunk that is refused before anything is added (empty, malformed, too long
// a proof, too many leaves) leaves the verifier usable; one that fails after
// adding breaks it for good.
do {
  let d = 9;
  let trees = [Peaks.withDepth(d, true), Peaks.withDepth(d, false), Peaks.withDepth(d, false)];
  let spareTree = Peaks.withDepth(d, true);
  for (n in ([1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 23, 31, 32, 33, 64, 100, 257] : [Nat]).values()) {
    let ls = leaves(n);
    let kinds : [(Peaks.Peaks, Peaks.Fill, Bool, [[Blob]], Blob)] = [
      (trees[0], #copy, true, Bitcoin.levels(ls), refBitcoin(ls)),
      (trees[1], #skip, false, Bagged.levels(ls), refBagged(ls)),
      (trees[2], padFill, false, Ssz.levels(ls, depth), refPadded(ls, depth)),
    ];
    for ((tree, fill, checked, levels, root) in kinds.values()) {
      for (step in ([1, 2, 3, 5, 8, 1000] : [Nat]).values()) {
        let v = Chunks.onTree(root, tree, null, fill, checked);
        assert v.count() == 0 and not v.broken();
        var m = 0;
        var s = step;
        while (m < n) {
          let m2 = if (m + s >= n) n else m + s;
          s := 1 + (s * 7 + m) % (2 * step);
          let chunk = slice(ls, m, m2);
          let p = Prove.rightPeaks(levels, m2);
          // refused up front: the verifier goes on
          assert not v.verifyChunk([], p);
          assert not v.verifyChunk(chunk, [("short" : Blob)]);
          assert not v.verifyChunk([("short" : Blob)], p);
          assert not v.verifyChunk(chunk, Array.tabulate<Blob>(d + 1, func(i) = leaf(900 + i)));
          assert not v.verifyChunk(Array.tabulate<Blob>(2 ** d + 1, func(i) = leaf(i)), []);
          assert not v.broken() and v.count() == m.toNat64();
          assert v.verifyChunk(chunk, p) and v.count() == m2.toNat64();
          m := m2;
        };
        assert v.complete() and not v.broken();
        assert not v.verifyChunk([ls[0]], []);
      };
      // a forged leaf, at each chunk in turn: refused, and nothing after it
      // is accepted, not even the honest chunk
      var cut = 0;
      while (cut < n) {
        let cut2 = if (cut + 5 >= n) n else cut + 5;
        let v = Chunks.onTree(root, tree, null, fill, checked);
        if (cut > 0) assert v.verifyChunk(slice(ls, 0, cut), Prove.rightPeaks(levels, cut));
        let chunk = slice(ls, cut, cut2);
        let p = Prove.rightPeaks(levels, cut2);
        assert not v.verifyChunk(Array.tabulate<Blob>(chunk.size(), func(i) = if (i == 0) flip(chunk[0]) else chunk[i]), p);
        assert v.broken() and not v.complete();
        assert not v.verifyChunk(chunk, p);
        cut := cut2;
      };
      // a wrong peak breaks it too
      if (n > 1) {
        let v = Chunks.onTree(root, tree, null, fill, checked);
        let p = Prove.rightPeaks(levels, 1);
        assert not v.verifyChunk([ls[0]], Array.tabulate<Blob>(p.size(), func(i) = if (i == 0) flip(p[0]) else p[i]));
        assert v.broken();
      };
    };
    // with a backup on the caller's trees: as `new`
    let v = Chunks.onTree(refBitcoin(ls), trees[0], ?spareTree, #copy, true);
    assert not v.verifyChunk(ls, [leaf(999)]) and not v.broken() and v.count() == 0;
    assert v.verifyChunk(ls, []) and v.complete();
  };
  // The presets' own form: their rules on the caller's tree, which serves
  // one verifier after another.
  let zTree = Ssz.new(depth);
  for (n in ([1, 2, 7, 23, 100] : [Nat]).values()) {
    let ls = leaves(n);
    let cut = (n + 1) / 2;
    let runs : [(Chunks.Verifier, [[Blob]])] = [
      (Bitcoin.verifierOn(refBitcoin(ls), trees[0]), Bitcoin.levels(ls)),
      (Bagged.verifierOn(refBagged(ls), trees[1]), Bagged.levels(ls)),
      (Ssz.verifierOn(refPadded(ls, depth), zTree), Ssz.levels(ls, depth)),
    ];
    for ((v, levels) in runs.values()) {
      assert v.count() == 0 and not v.complete();
      assert v.verifyChunk(slice(ls, 0, cut), Prove.rightPeaks(levels, cut));
      if (cut < n) assert v.verifyChunk(slice(ls, cut, n), []);
      assert v.count() == n.toNat64() and not v.broken();
    };
    assert runs[0].0.complete() and runs[1].0.complete();
    // as the verifiers with a backup, these check for equal siblings in Bitcoin only
    if (n >= 2) {
      let twice = Array.tabulate<Blob>(n, func(i) = if (i == 1) ls[0] else ls[i]);
      assert not Bitcoin.verifierOn(refBitcoin(twice), trees[0]).verifyChunk(twice, []);
      assert Bagged.verifierOn(refBagged(twice), trees[1]).verifyChunk(twice, []);
      assert Ssz.verifierOn(refPadded(twice, depth), zTree).verifyChunk(twice, []);
    };
    // the tree of a zero-padded verifier is still the caller's tree
    assert zTree.count() == n.toNat64();
  };

  // A proof may have one peak per level and no more: 8 leaves, the first one
  // sent alone, in a verifier of depth 3.
  let eight = leaves(8);
  let levels = Bitcoin.levels(eight);
  let p = Prove.rightPeaks(levels, 1);
  assert p.size() == 3;
  let v = Bitcoin.verifier(refBitcoin(eight), 3);
  assert not v.verifyChunk([eight[0]], p.concat([leaf(999)]));
  assert v.verifyChunk([eight[0]], p);
  assert v.verifyChunk(slice(eight, 1, 8), []) and v.complete();
};

// --- Bitcoin: mutated lists and equal siblings ---
let bare = Peaks.withDepth(10, true); // a caller's tree for verifiers without a backup
for (n in ([2, 3, 5, 6, 7, 11, 12, 13, 16, 100] : [Nat]).values()) {
  let ls = leaves(n);
  let root = refBitcoin(ls);
  assert not Bitcoin.mutated(ls);
  var width = 1;
  while (width < n) {
    if (n % (2 * width) == width) {
      // the last 2^k leaves written out twice: the same root
      let mutated = ls.concat(slice(ls, n - width, n));
      assert refBitcoin(mutated) == root and Bitcoin.mutated(mutated);
      // the plain tree hashes it all the same; the checked one stops
      let plain = Bitcoin.new(2 * n);
      let checked = Bitcoin.new(2 * n);
      var ok = true;
      for (l in mutated.values()) {
        Bitcoin.add(plain, l);
        if (ok and not Bitcoin.addChecked(checked, l)) ok := false;
      };
      assert Bitcoin.root(plain) == root and not ok;
      // the chunk verifier rejects it, in one chunk and split anywhere
      let levels = Bitcoin.levels(mutated);
      // (an odd cut makes the second chunk start with a single leaf), with
      // and without a backup
      for (cut in Nat.range(1, mutated.size() + 1)) {
        for (v in [Bitcoin.verifier(root, 10), Chunks.onTree(root, bare, null, #copy, true)].values()) {
          if (cut == mutated.size()) {
            assert not v.verifyChunk(mutated, []);
          } else {
            assert not (v.verifyChunk(slice(mutated, 0, cut), Prove.rightPeaks(levels, cut)) and v.verifyChunk(slice(mutated, cut, mutated.size()), []));
          };
        };
      };
    };
    width *= 2;
  };
};
do {
  let t = leaves(6);
  let (a, b, c, d) = (t[0], t[1], t[2], t[3]);
  func h(x : Blob, y : Blob) : Blob = dsha(x, y);
  func rejects(list : [Blob], chunk : [Blob], proof : [Blob]) : Bool {
    let v = Bitcoin.verifier(refBitcoin(list), 10);
    let w = Chunks.onTree(refBitcoin(list), bare, null, #copy, true);
    not v.verifyChunk(chunk, proof) and v.count() == 0 and not w.verifyChunk(chunk, proof) and w.broken();
  };
  // equal siblings in adding: two leaves, and two nodes one level up
  assert rejects([a, a, b, c], [a, a, b, c], []);
  assert rejects([a, b, a, b, c, d], [a, b, a, b, c, d], []);
  // in closing, against a peak of the tree
  assert rejects([a, b, a, b], [a, b, a], [b]);
  // in closing, against a peak of the proof: at the lowest peak, and higher up
  assert rejects([a, b, a, b], [a, b], [h(a, b)]);
  assert rejects([a, b, c, d, a, b, c, d], [a, b, c], [d, h(h(a, b), h(c, d))]);
  assert rejects([a, a], [a], [a]);
  // an honest block: the proof may not name what Bitcoin would duplicate
  let five = slice(t, 0, 5);
  let v5 = Bitcoin.verifier(refBitcoin(five), 10);
  assert not v5.verifyChunk(five, [t[4]]);
  assert v5.verifyChunk(five, []) and v5.complete();
  let v6 = Bitcoin.verifier(refBitcoin(t), 10);
  assert not v6.verifyChunk(t, [h(t[4], t[5])]);
  assert v6.verifyChunk(t, []) and v6.complete();
  // pairs: the checked form refuses two equal leaves, and the same pair
  // twice, which would be two equal nodes one level up
  let p = Peaks.new(8, true);
  assert not p.addPairChecked(a, a) and p.count == 0;
  assert p.addPairChecked(a, b) and p.count == 2;
  assert not p.addPairChecked(a, b) and p.count == 2;
  assert p.addPairChecked(c, d) and p.root(#copy) == refBitcoin([a, b, c, d]);
};

// --- The known limit: a whole level verifies as a shorter list ---
do {
  let eight = leaves(8);
  let level1 = Array.tabulate<Blob>(4, func(i) = dsha(eight[2 * i], eight[2 * i + 1]));
  assert Bitcoin.merkleRoot(level1) == refBitcoin(eight);
  let v = Bitcoin.verifier(refBitcoin(eight), 10);
  assert v.verifyChunk(level1, []) and v.complete() and v.count() == 4;
};

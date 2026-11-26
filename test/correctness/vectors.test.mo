// @testmode wasi
// Known answers: the roots of the package against vectors computed by an
// independent implementation in another language, against constants of the
// SSZ specification, and against real Bitcoin blocks.
import Peaks "../../src/Peaks";
import Bitcoin "../../src/Bitcoin";
import Bagged "../../src/Bagged";
import Ssz "../../src/Ssz";
import Array "mo:core/Array";
import Blob "mo:core/Blob";
import Fixtures "../support/Fixtures";

let { leaf; leaves; hex } = Fixtures;

// Vectors from an independent implementation.
//
// Each row is (n, Bitcoin root, bagged root, zero-padded root at depth 7, the
// same with the length mixed in) over the n leaves SHA256("leaf0"),
// SHA256("leaf1"), ... The sizes cover the powers of two and their
// neighbours, where the carries of the tree are longest.
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
    // the same roots from a tree that is filled leaf by leaf
    let t = Ssz.new(7);
    for (l in ls.values()) Ssz.add(t, l);
    assert Ssz.root(t) == hex(padded) and Ssz.rootWithLength(t) == hex(withLength);
    assert Ssz.mixInLength(hex(padded), n) == hex(withLength);
  };
};

// Constants of the SSZ specification.
//
// The first zero hashes, and the root of the empty deposit tree: depth 32,
// as in the Ethereum deposit contract.
do {
  let z = Peaks.zeros(32, false);
  assert z.size() == 33 and z[0].size() == 32;
  assert z[1] == hex("f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b");
  assert z[2] == hex("db56114e00fdd4c1f85c892bf35ac9a89289aaecb1ebd0a96cde606a748b5d71");
  let deposits = Ssz.new(32);
  assert Ssz.root(deposits) == z[32];
  assert Ssz.rootWithLength(deposits) == hex("d70a234731285c6804c2a4f56711ddb8c82c99740f207854891028af34e27e5e");
  assert Ssz.merkleize([], null) == z[0];
};

// Real Bitcoin blocks.
//
// Block 170 of the mainnet has 2 transactions. Block 586 has 3, so its last
// node is paired with itself. The txids and the roots are in internal byte
// order, which is the display hex reversed.
do {
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

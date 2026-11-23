// @testmode wasi
// The code of the README, compiled and run, so that the examples there stay true.
import Bitcoin "../src/Bitcoin";
import Bagged "../src/Bagged";
import Ssz "../src/Ssz";
import Chunks "../src/Chunks";
import Prove "../src/Prove";
import Sha256 "mo:sha2/Sha256";
import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Text "mo:core/Text";

let txids = Array.tabulate<Blob>(11, func(i) = Sha256.fromBlob(("tx" # i.toText()).encodeUtf8()));

// Bitcoin
do {
  let root = Bitcoin.merkleRoot(txids);

  let tree = Bitcoin.new(10_000);
  for (txid in txids.values()) tree.add(txid);
  let sameRoot = tree.root();
  assert sameRoot == root;

  let levels = Bitcoin.levels(txids);
  let index = 7;
  let txid = txids[index];
  let branch = Prove.branch(levels, index, #copy);
  let ok = Bitcoin.verifyBranch(txid, index, branch, root);
  assert ok;
};

// Bagged
do {
  let chunks : [Blob] = ["first chunk", "second chunk", "third chunk"];
  let tree = Bagged.new(1_000_000);
  let digest = Sha256.new();
  for (chunk in chunks.values()) tree.addMessage(digest, chunk);
  let root = tree.root();

  let leaves = chunks.map<Blob, Blob>(func(c) = Sha256.fromBlob(c));
  let (index, size) = (1, 3);
  let path = Prove.branch(Bagged.levels(leaves), index, #skip);
  let ok = Bagged.verifyInclusion(leaves[index], index, size, path, root);
  assert ok;
};

// Zero-padded (SSZ)
do {
  let chunks = txids;
  let tree = Ssz.new(32);
  for (chunk in chunks.values()) tree.add(chunk);
  let root = tree.root();
  let listRoot = tree.rootWithLength();
  assert listRoot == Ssz.mixInLength(root, chunks.size());

  let index = 3;
  let branch = Prove.branch(Ssz.levels(chunks, 32), index, Ssz.fillOf(32));
  let ok = Ssz.verifyBranch(chunks[index], index, branch, root);
  assert ok;
};

// Verifying in chunks
do {
  let root = Bitcoin.merkleRoot(txids);
  let levels = Bitcoin.levels(txids);
  let verifier = Bitcoin.verifier(root, 14);
  for ((from, to) in ([(0, 4), (4, 9), (9, 11)] : [(Nat, Nat)]).values()) {
    let chunk = Array.tabulate<Blob>(to - from, func(i) = txids[from + i]);
    let proof = Prove.rightPeaks(levels, to);
    if (not verifier.verifyChunk(chunk, proof)) assert false;
    assert verifier.complete() == (to == 11);
  };
};

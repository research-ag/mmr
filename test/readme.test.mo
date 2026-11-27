// @testmode wasi
// The code of the README, compiled and run, so that the examples there stay true.
import Bitcoin "../src/Bitcoin";
import Bagged "../src/Bagged";
import ZeroPadded "../src/ZeroPadded";
import Chunks "../src/Chunks";
import Peaks "../src/Peaks";
import MerkleTree "../src/MerkleTree";
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

  let index = 7;
  let txid = txids[index];
  let branch = Bitcoin.merkleTree(txids).branch(index);
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
  let path = Bagged.merkleTree(leaves).branch(index);
  let ok = Bagged.verifyInclusion(leaves[index], index, size, path, root);
  assert ok;
};

// Zero-padded
do {
  let chunks = txids;
  let tree = ZeroPadded.new(32);
  for (chunk in chunks.values()) tree.add(chunk);
  let root = tree.root();
  let listRoot = tree.rootWithLength();
  assert listRoot == ZeroPadded.mixInLength(root, chunks.size());

  let index = 3;
  let branch = ZeroPadded.merkleTree(chunks, 32).branch(index);
  let ok = ZeroPadded.verifyBranch(chunks[index], index, branch, root);
  assert ok;
};

// Verifying in chunks
do {
  let root = Bitcoin.merkleRoot(txids);
  let full = Bitcoin.merkleTree(txids);
  let verifier = Bitcoin.verifier(root, 14);
  for ((from, to) in ([(0, 4), (4, 9), (9, 11)] : [(Nat, Nat)]).values()) {
    let chunk = Array.tabulate<Blob>(to - from, func(i) = txids[from + i]);
    let proof = full.rightPeaks(to);
    if (not verifier.verifyChunk(chunk, proof)) assert false;
    assert verifier.complete() == (to == 11);
  };
};

// On one tree for all uploads
do {
  let root = Bitcoin.merkleRoot(txids);
  let full = Bitcoin.merkleTree(txids);
  let tree = Bitcoin.withDepth(14);
  for (upload in Nat.range(0, 2)) {
    let verifier = Bitcoin.verifierOn(root, tree);
    for ((from, to) in ([(0, 3), (3, 11)] : [(Nat, Nat)]).values()) {
      let chunk = Array.tabulate<Blob>(to - from, func(i) = txids[from + i]);
      let proof = full.rightPeaks(to);
      if (not verifier.verifyChunk(chunk, proof)) assert false;
    };
    assert verifier.complete() and not verifier.broken();
  };
};

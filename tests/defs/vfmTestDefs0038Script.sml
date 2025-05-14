open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0038";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_opcodes.json";
val defs = mapi (define_test "0038") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0036";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_gasprice_opcode.json";
val defs = mapi (define_test "0036") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0035";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/blob_txs/blob_gas_subtraction_tx.json";
val defs = mapi (define_test "0035") tests;
val () = export_theory_no_docs ();

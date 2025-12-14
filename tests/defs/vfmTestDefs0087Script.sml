open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0087";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_tx_entry_point.json";
val defs = mapi (define_test "0087") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0153";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_tx_nonce.json";
val defs = mapi (define_test "0153") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0361";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_non_empty_storage_non_zero_nonce.json";
val defs = mapi (define_test "0361") tests;
val () = export_theory_no_docs ();

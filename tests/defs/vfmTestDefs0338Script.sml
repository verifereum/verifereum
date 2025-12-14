open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0338";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_resets_an_empty_code_account_with_storage.json";
val defs = mapi (define_test "0338") tests;
val () = export_theory_no_docs ();

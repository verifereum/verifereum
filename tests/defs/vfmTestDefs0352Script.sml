open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0352";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_from_account_with_non_delegating_code.json";
val defs = mapi (define_test "0352") tests;
val () = export_theory_no_docs ();

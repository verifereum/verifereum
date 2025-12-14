open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0319";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_empty_authorization_list.json";
val defs = mapi (define_test "0319") tests;
val () = export_theory_no_docs ();

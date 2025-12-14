open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0350";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_all_invalid_authorization_tuples.json";
val defs = mapi (define_test "0350") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0339";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_reverts.json";
val defs = mapi (define_test "0339") tests;
val () = export_theory_no_docs ();

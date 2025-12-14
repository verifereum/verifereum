open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0371";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_to_tstore_reentry.json";
val defs = mapi (define_test "0371") tests;
val () = export_theory_no_docs ();

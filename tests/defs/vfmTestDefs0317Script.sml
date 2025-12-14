open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0317";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_double_auth.json";
val defs = mapi (define_test "0317") tests;
val () = export_theory_no_docs ();

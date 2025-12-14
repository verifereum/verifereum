open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0305";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_to_pre_authorized_oog.json";
val defs = mapi (define_test "0305") tests;
val () = export_theory_no_docs ();

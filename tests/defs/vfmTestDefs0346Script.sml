open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0346";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_self_set_code_cost.json";
val defs = mapi (define_test "0346") tests;
val () = export_theory_no_docs ();

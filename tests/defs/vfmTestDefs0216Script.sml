open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0216";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/gas/self_set_code_cost.json";
val defs = mapi (define_test "0216") tests;
val () = export_theory_no_docs ();

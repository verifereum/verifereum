open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0214";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/gas/gas_cost.json";
val defs = mapi (define_test "0214") tests;
val () = export_theory_no_docs ();

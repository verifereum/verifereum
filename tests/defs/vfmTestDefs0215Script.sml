open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0215";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/gas/intrinsic_gas_cost.json";
val defs = mapi (define_test "0215") tests;
val () = export_theory_no_docs ();

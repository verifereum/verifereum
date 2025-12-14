open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0005";
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2930_access_list/test_transaction_intrinsic_gas_cost.json";
val defs = mapi (define_test "0005") tests;
val () = export_theory_no_docs ();

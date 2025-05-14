open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0205";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_1_type_2.json";
val defs = mapi (define_test "0205") tests;
val () = export_theory_no_docs ();

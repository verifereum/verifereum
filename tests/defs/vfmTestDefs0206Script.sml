open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0206";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_3.json";
val defs = mapi (define_test "0206") tests;
val () = export_theory_no_docs ();

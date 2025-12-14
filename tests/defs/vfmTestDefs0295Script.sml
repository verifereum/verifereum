open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0295";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_transaction_validity_type_4.json";
val defs = mapi (define_test "0295") tests;
val () = export_theory_no_docs ();

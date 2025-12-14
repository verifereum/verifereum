open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0172";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_maximum_gas_refund.json";
val defs = mapi (define_test "0172") tests;
val () = export_theory_no_docs ();

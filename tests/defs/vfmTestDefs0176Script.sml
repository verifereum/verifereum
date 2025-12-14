open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0176";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_limit_cap_access_list_with_diff_addr.json";
val defs = mapi (define_test "0176") tests;
val () = export_theory_no_docs ();

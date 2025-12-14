open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0181";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_limit_cap_exceeded.json";
val defs = mapi (define_test "0181") tests;
val () = export_theory_no_docs ();

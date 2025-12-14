open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0163";
val tests = json_path_to_tests "../fixtures/blockchain_tests/london/eip1559_fee_market_change/test_eip1559_tx_validity.json";
val defs = mapi (define_test "0163") tests;
val () = export_theory_no_docs ();

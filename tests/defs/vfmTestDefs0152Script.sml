open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0152";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/validation/test_tx_gas_limit.json";
val defs = mapi (define_test "0152") tests;
val () = export_theory_no_docs ();

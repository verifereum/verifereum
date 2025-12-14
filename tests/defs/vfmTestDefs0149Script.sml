open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0149";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/touch/test_zero_gas_price_and_touching.json";
val defs = mapi (define_test "0149") tests;
val () = export_theory_no_docs ();

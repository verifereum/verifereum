open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0200";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_various_base_fee_scenarios.json";
val defs = mapi (define_test "0200") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0198";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_at_transition.json";
val defs = mapi (define_test "0198") tests;
val () = export_theory_no_docs ();

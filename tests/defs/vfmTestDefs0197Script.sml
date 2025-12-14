open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0197";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_blob_base_fee_with_bpo_transition.json";
val defs = mapi (define_test "0197") tests;
val () = export_theory_no_docs ();

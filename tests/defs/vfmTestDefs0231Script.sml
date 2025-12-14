open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0231";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_wycheproof_extra.json";
val defs = mapi (define_test "0231") tests;
val () = export_theory_no_docs ();

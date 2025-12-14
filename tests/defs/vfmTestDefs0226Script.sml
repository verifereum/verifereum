open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0226";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_modular_comparison.json";
val defs = mapi (define_test "0226") tests;
val () = export_theory_no_docs ();

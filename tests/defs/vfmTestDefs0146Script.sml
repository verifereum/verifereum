open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0146";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/precompiles/test_precompile_absence.json";
val defs = mapi (define_test "0146") tests;
val () = export_theory_no_docs ();

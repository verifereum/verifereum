open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0147";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/precompiles/test_precompiles.json";
val defs = mapi (define_test "0147") tests;
val () = export_theory_no_docs ();

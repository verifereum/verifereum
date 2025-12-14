open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0116";
val tests = json_path_to_tests "../fixtures/blockchain_tests/constantinople/eip1014_create2/test_recreate.json";
val defs = mapi (define_test "0116") tests;
val () = export_theory_no_docs ();

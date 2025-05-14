open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0811";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeSizeLimit/create2CodeSizeLimit.json";
val defs = mapi (define_test "0811") tests;
val () = export_theory_no_docs ();

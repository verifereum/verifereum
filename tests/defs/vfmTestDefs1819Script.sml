open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1819";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRecursiveCreate/recursiveCreateReturnValue.json";
val defs = mapi (define_test "1819") tests;
val () = export_theory_no_docs ();

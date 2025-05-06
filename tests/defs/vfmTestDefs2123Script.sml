open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2123";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/CallRecursiveMethods.json";
val defs = mapi (define_test "2123") tests;
val () = export_theory_no_docs ();

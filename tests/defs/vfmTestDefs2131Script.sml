open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2131";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestCryptographicFunctions.json";
val defs = mapi (define_test "2131") tests;
val () = export_theory_no_docs ();

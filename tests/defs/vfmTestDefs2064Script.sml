open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2064";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/block504980.json";
val defs = mapi (define_test "2064") tests;
val () = export_theory_no_docs ();

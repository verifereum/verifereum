open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2032";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/makeMoney.json";
val defs = mapi (define_test "2032") tests;
val () = export_theory_no_docs ();

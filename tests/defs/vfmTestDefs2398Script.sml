open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2398";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/doubleSelfdestructTouch_Paris.json";
val defs = mapi (define_test "2398") tests;
val () = export_theory_no_docs ();

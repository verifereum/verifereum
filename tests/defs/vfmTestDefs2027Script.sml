open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2027";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrecompiledTouch_Paris.json";
val defs = mapi (define_test "2027") tests;
val () = export_theory_no_docs ();

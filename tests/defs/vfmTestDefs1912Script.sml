open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1912";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrecompiledTouch_storage_Paris.json";
val defs = mapi (define_test "1912") tests;
val () = export_theory_no_docs ();

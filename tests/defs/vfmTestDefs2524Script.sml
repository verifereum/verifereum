open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2524";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_SUICIDE_ToOneStorageKey_OOGRevert_Paris.json";
val defs = mapi (define_test "2524") tests;
val () = export_theory_no_docs ();

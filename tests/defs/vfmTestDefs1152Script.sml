open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1152";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_DELEGATECALL_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "1152") tests;
val () = export_theory_no_docs ();

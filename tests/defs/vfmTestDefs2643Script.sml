open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2643";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_CALLCODE_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "2643") tests;
val () = export_theory_no_docs ();

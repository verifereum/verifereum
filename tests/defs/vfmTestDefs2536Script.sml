open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2536";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_DELEGATECALL_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "2536") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2534";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_DELEGATECALL_ToEmpty_Paris.json";
val defs = mapi (define_test "2534") tests;
val () = export_theory_no_docs ();

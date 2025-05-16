open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2518";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_DELEGATECALL_ToEmpty_OOGRevert_Paris.json";
val defs = mapi (define_test "2518") tests;
val () = export_theory_no_docs ();

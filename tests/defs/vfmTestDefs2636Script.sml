open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2636";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_SUICIDE_ToEmpty_OOGRevert_Paris.json";
val defs = mapi (define_test "2636") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2538";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_SUICIDE_ToEmpty_Paris.json";
val defs = mapi (define_test "2538") tests;
val () = export_theory_no_docs ();

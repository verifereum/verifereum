open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2657";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_SUICIDE_ToNonZeroBalance.json";
val defs = mapi (define_test "2657") tests;
val () = export_theory_no_docs ();

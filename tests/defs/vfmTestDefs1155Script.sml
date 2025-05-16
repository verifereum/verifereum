open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1155";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_SUICIDE_ToNonNonZeroBalance.json";
val defs = mapi (define_test "1155") tests;
val () = export_theory_no_docs ();

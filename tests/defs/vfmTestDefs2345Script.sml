open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2345";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/StaticcallForPrecompilesIssue683.json";
val defs = mapi (define_test "2345") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1904";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_following_successful_create.json";
val defs = mapi (define_test "1904") tests;
val () = export_theory_no_docs ();

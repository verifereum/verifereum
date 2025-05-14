open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1982";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_following_too_big_transfer.json";
val defs = mapi (define_test "1982") tests;
val () = export_theory_no_docs ();

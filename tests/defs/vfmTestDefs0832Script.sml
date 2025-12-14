open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0832";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/returndatacopy_following_revert_in_create.json";
val defs = mapi (define_test "0832") tests;
val () = export_theory_no_docs ();

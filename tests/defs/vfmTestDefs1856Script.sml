open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1856";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_successful_delegatecall.json";
val defs = mapi (define_test "1856") tests;
val () = export_theory_no_docs ();

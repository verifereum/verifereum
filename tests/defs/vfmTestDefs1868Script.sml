open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1868";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_overrun.json";
val defs = mapi (define_test "1868") tests;
val () = export_theory_no_docs ();

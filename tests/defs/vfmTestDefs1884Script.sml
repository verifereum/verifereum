open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1884";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/LoopCallsDepthThenRevert2.json";
val defs = mapi (define_test "1884") tests;
val () = export_theory_no_docs ();

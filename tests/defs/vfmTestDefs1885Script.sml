open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1885";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/LoopCallsDepthThenRevert3.json";
val defs = mapi (define_test "1885") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1887";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/LoopDelegateCallsDepthThenRevert.json";
val defs = mapi (define_test "1887") tests;
val () = export_theory_no_docs ();

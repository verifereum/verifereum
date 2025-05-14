open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2001";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/LoopCallsDepthThenRevert.json";
val defs = mapi (define_test "2001") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2155";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_LoopCallsThenRevert.json";
val defs = mapi (define_test "2155") tests;
val () = export_theory_no_docs ();

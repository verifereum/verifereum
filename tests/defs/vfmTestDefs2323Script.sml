open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2323";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log1_MaxTopic.json";
val defs = mapi (define_test "2323") tests;
val () = export_theory_no_docs ();

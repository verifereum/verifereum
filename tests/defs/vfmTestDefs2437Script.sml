open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2437";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log1_MaxTopic.json";
val defs = mapi (define_test "2437") tests;
val () = export_theory_no_docs ();

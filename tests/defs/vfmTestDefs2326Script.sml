open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2326";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log1_logMemsizeTooHigh.json";
val defs = mapi (define_test "2326") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2318";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log0_logMemsizeTooHigh.json";
val defs = mapi (define_test "2318") tests;
val () = export_theory_no_docs ();

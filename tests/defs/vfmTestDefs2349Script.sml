open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2349";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_calldelcode_01.json";
val defs = mapi (define_test "2349") tests;
val () = export_theory_no_docs ();

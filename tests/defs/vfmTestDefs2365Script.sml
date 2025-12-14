open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2365";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log_Caller.json";
val defs = mapi (define_test "2365") tests;
val () = export_theory_no_docs ();

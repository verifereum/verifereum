open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2053";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ABAcalls3.json";
val defs = mapi (define_test "2053") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2051";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ABAcalls1.json";
val defs = mapi (define_test "2051") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2186";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_call_OOG_additionalGasCosts1.json";
val defs = mapi (define_test "2186") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2187";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_call_OOG_additionalGasCosts2_Paris.json";
val defs = mapi (define_test "2187") tests;
val () = export_theory_no_docs ();

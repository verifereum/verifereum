open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2148";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ExecuteCallThatAskForeGasThenTrabsactionHas.json";
val defs = mapi (define_test "2148") tests;
val () = export_theory_no_docs ();

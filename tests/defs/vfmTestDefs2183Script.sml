open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2183";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callWithHighValueAndGasOOG.json";
val defs = mapi (define_test "2183") tests;
val () = export_theory_no_docs ();

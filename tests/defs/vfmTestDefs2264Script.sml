open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2264";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_InternalCallHittingGasLimit2.json";
val defs = mapi (define_test "2264") tests;
val () = export_theory_no_docs ();

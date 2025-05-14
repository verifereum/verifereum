open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2449";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_refund_CallToSuicideNoStorage.json";
val defs = mapi (define_test "2449") tests;
val () = export_theory_no_docs ();

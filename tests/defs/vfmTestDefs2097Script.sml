open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2097";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecoverCheckLengthWrongV.json";
val defs = mapi (define_test "2097") tests;
val () = export_theory_no_docs ();

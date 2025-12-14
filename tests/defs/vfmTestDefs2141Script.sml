open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2141";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallIdentitiy_1.json";
val defs = mapi (define_test "2141") tests;
val () = export_theory_no_docs ();

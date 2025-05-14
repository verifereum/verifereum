open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2172";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ABAcallsSuicide0.json";
val defs = mapi (define_test "2172") tests;
val () = export_theory_no_docs ();

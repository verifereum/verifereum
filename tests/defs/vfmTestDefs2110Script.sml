open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2110";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallIdentity_4_gas18.json";
val defs = mapi (define_test "2110") tests;
val () = export_theory_no_docs ();

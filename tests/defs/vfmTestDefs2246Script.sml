open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2246";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRipemd160_4_gas719.json";
val defs = mapi (define_test "2246") tests;
val () = export_theory_no_docs ();

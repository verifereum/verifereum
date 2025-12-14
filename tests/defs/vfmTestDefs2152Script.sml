open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2152";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRecursiveBomb1.json";
val defs = mapi (define_test "2152") tests;
val () = export_theory_no_docs ();

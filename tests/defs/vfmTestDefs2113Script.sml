open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2113";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRecursiveBomb0.json";
val defs = mapi (define_test "2113") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2244";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallSha256_1.json";
val defs = mapi (define_test "2244") tests;
val () = export_theory_no_docs ();

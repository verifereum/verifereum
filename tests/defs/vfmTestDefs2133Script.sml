open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2133";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallSha256_3.json";
val defs = mapi (define_test "2133") tests;
val () = export_theory_no_docs ();

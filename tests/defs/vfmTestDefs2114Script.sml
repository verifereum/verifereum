open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2114";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000bytesContract50_2.json";
val defs = mapi (define_test "2114") tests;
val () = export_theory_no_docs ();

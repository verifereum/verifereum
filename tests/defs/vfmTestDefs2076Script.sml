open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2076";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000bytesContract50_1.json";
val defs = mapi (define_test "2076") tests;
val () = export_theory_no_docs ();

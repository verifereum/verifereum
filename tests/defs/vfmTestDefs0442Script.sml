open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0442";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/eip2315NotRemoved.json";
val defs = mapi (define_test "0442") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0989";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/add11.json";
val defs = mapi (define_test "0989") tests;
val () = export_theory_no_docs ();

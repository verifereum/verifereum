open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0705";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/Create2OOGFromCallRefunds.json";
val defs = mapi (define_test "0705") tests;
val () = export_theory_no_docs ();

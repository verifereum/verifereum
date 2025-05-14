open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0324";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP5656_MCOPY/MCOPY.json";
val defs = mapi (define_test "0324") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0886";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/typeTwoBerlin.json";
val defs = mapi (define_test "0886") tests;
val () = export_theory_no_docs ();

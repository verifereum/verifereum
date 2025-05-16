open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0833";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_d64m1.json";
val defs = mapi (define_test "0833") tests;
val () = export_theory_no_docs ();

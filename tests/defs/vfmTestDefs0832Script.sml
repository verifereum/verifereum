open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0832";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_d64e0.json";
val defs = mapi (define_test "0832") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0881";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/outOfFunds.json";
val defs = mapi (define_test "0881") tests;
val () = export_theory_no_docs ();

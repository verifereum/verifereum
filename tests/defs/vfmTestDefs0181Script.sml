open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0181";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/deposits/deposit_negative.json";
val defs = mapi (define_test "0181") tests;
val () = export_theory_no_docs ();

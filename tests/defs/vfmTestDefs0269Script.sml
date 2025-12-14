open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0269";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_deposit_negative.json";
val defs = mapi (define_test "0269") tests;
val () = export_theory_no_docs ();

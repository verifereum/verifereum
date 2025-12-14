open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0268";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_deposit.json";
val defs = mapi (define_test "0268") tests;
val () = export_theory_no_docs ();

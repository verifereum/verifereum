open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0270";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_eip_6110.json";
val defs = mapi (define_test "0270") tests;
val () = export_theory_no_docs ();

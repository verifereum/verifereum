open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0272";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_invalid_layout.json";
val defs = mapi (define_test "0272") tests;
val () = export_theory_no_docs ();

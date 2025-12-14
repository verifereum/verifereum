open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0102";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_dynamic_create2_selfdestruct_collision_two_different_transactions.json";
val defs = mapi (define_test "0102") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0100";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_dynamic_create2_selfdestruct_collision.json";
val defs = mapi (define_test "0100") tests;
val () = export_theory_no_docs ();

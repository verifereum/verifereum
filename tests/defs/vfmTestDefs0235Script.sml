open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0235";
val tests = json_path_to_tests "../fixtures/blockchain_tests/paris/eip7610_create_collision/test_init_collision_create_tx.json";
val defs = mapi (define_test "0235") tests;
val () = export_theory_no_docs ();

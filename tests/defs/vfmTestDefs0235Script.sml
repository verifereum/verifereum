Theory vfmTestDefs0235[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/paris/eip7610_create_collision/test_init_collision_create_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/paris/eip7610_create_collision/test_init_collision_create_tx.json");
val defs = mapi (define_test "0235") tests;

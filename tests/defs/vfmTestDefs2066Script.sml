Theory vfmTestDefs2066[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_hash_collision/create_hash_collision.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_hash_collision/create_hash_collision.json");
val defs = mapi (define_test "2066") tests;

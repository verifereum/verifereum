Theory vfmTestDefs0637[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/revert_depth_create_address_collision/revert_depth_create_address_collision.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/revert_depth_create_address_collision/revert_depth_create_address_collision.json");
val defs = mapi (define_test "0637") tests;

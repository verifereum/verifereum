Theory vfmTestDefs0985[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/collision_selfdestruct/selfdestruct_after_create2_collision.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/collision_selfdestruct/selfdestruct_after_create2_collision.json");
val defs = mapi (define_test "0985") tests;

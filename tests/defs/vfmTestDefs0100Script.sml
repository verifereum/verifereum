Theory vfmTestDefs0100[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_dynamic_create2_selfdestruct_collision.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip6780_selfdestruct/test_dynamic_create2_selfdestruct_collision.json");
val defs = mapi (define_test "0100") tests;

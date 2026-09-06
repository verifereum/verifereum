Theory vfmTestDefs0119[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/dynamic_create2_selfdestruct_collision/dynamic_create2_selfdestruct_collision_two_different_transactions.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/dynamic_create2_selfdestruct_collision/dynamic_create2_selfdestruct_collision_two_different_transactions.json");
val defs = mapi (define_test "0119") tests;

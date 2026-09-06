Theory vfmTestDefs0121[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/reentrancy_selfdestruct_revert/reentrancy_selfdestruct_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip6780_selfdestruct/reentrancy_selfdestruct_revert/reentrancy_selfdestruct_revert.json");
val defs = mapi (define_test "0121") tests;

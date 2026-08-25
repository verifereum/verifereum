Theory vfmTestDefs0110[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_pre_existing.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_pre_existing.json");
val defs = mapi (define_test "0110") tests;

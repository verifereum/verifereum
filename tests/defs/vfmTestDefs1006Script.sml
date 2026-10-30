Theory vfmTestDefs1006[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct_finalization/selfdestruct_clears_nonce_and_storage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct_finalization/selfdestruct_clears_nonce_and_storage.json");
val defs = mapi (define_test "1006") tests;

Theory vfmTestDefs0330[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/eip_mainnet/bal_storage_and_value_mainnet.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7928_block_level_access_lists/eip_mainnet/bal_storage_and_value_mainnet.json");
val defs = mapi (define_test "0330") tests;

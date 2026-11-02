Theory vfmTestDefs0838[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8246_selfdestruct_no_burn/eip_mainnet/create_tx_selfdestruct_to_self_keeps_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8246_selfdestruct_no_burn/eip_mainnet/create_tx_selfdestruct_to_self_keeps_balance.json");
val defs = mapi (define_test "0838") tests;

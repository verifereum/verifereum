Theory vfmTestDefs0064[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/eip_mainnet/simple_transfer_mainnet.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/eip_mainnet/simple_transfer_mainnet.json");
val defs = mapi (define_test "0064") tests;

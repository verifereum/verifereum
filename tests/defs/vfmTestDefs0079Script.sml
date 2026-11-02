Theory vfmTestDefs0079[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/delegatecall_inner_call_with_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/delegatecall_inner_call_with_value.json");
val defs = mapi (define_test "0079") tests;

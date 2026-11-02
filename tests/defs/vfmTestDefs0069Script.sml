Theory vfmTestDefs0069[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/call_with_value_to_coinbase_no_priority_fee_log.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/call_with_value_to_coinbase_no_priority_fee_log.json");
val defs = mapi (define_test "0069") tests;

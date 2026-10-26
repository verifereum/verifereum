Theory vfmTestDefs0066[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/call_opcodes_transfer_log_behavior.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/call_opcodes_transfer_log_behavior.json");
val defs = mapi (define_test "0066") tests;

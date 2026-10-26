Theory vfmTestDefs0082[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/failed_inner_operation_no_log.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/failed_inner_operation_no_log.json");
val defs = mapi (define_test "0082") tests;

Theory vfmTestDefs0085[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/inner_create_succeeds_outer_reverts_no_log.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7708_eth_transfer_logs/transfer_logs/inner_create_succeeds_outer_reverts_no_log.json");
val defs = mapi (define_test "0085") tests;

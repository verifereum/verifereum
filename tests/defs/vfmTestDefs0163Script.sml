Theory vfmTestDefs0163[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/london/eip1559_fee_market_change/test_eip1559_tx_validity.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/london/eip1559_fee_market_change/test_eip1559_tx_validity.json");
val defs = mapi (define_test "0163") tests;

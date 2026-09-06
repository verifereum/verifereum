Theory vfmTestDefs0235[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/london/eip1559_fee_market_change/tx_type/invalid_chain_id.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/london/eip1559_fee_market_change/tx_type/invalid_chain_id.json");
val defs = mapi (define_test "0235") tests;

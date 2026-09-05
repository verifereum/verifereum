Theory vfmTestDefs0444[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/call_with_high_value_and_oo_gat_tx_level/call_with_high_value_and_oo_gat_tx_level.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/call_with_high_value_and_oo_gat_tx_level/call_with_high_value_and_oo_gat_tx_level.json");
val defs = mapi (define_test "0444") tests;

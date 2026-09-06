Theory vfmTestDefs0684[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/callcode_with_high_value_and_gas_oog/callcode_with_high_value_and_gas_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/callcode_with_high_value_and_gas_oog/callcode_with_high_value_and_gas_oog.json");
val defs = mapi (define_test "0684") tests;

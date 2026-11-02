Theory vfmTestDefs2559[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_with_high_value_and_gas_oog/static_call_with_high_value_and_gas_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_with_high_value_and_gas_oog/static_call_with_high_value_and_gas_oog.json");
val defs = mapi (define_test "2559") tests;

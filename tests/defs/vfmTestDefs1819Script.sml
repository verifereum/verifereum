Theory vfmTestDefs1819[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_oog_additional_gas_costs2_paris/static_call_oog_additional_gas_costs2_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_oog_additional_gas_costs2_paris/static_call_oog_additional_gas_costs2_paris.json");
val defs = mapi (define_test "1819") tests;

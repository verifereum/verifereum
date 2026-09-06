Theory vfmTestDefs2014[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_raw_call_gas_ask/static_raw_call_gas_ask.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_raw_call_gas_ask/static_raw_call_gas_ask.json");
val defs = mapi (define_test "2014") tests;

Theory vfmTestDefs1994[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_internal_call_hitting_gas_limit/static_internal_call_hitting_gas_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_internal_call_hitting_gas_limit/static_internal_call_hitting_gas_limit.json");
val defs = mapi (define_test "1994") tests;

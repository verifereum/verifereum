Theory vfmTestDefs0856[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemExpandingEIP150Calls/new_gas_price_for_codes_with_mem_expanding_calls/new_gas_price_for_codes_with_mem_expanding_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemExpandingEIP150Calls/new_gas_price_for_codes_with_mem_expanding_calls/new_gas_price_for_codes_with_mem_expanding_calls.json");
val defs = mapi (define_test "0856") tests;

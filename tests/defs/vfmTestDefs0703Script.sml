Theory vfmTestDefs0703[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/call_asks_more_gas_than_available/top_frame_asks_more_gas_than_available.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/call_asks_more_gas_than_available/top_frame_asks_more_gas_than_available.json");
val defs = mapi (define_test "0703") tests;

Theory vfmTestDefs1796[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_ecrecover0_no_gas/static_call_ecrecover0_no_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_ecrecover0_no_gas/static_call_ecrecover0_no_gas.json");
val defs = mapi (define_test "1796") tests;

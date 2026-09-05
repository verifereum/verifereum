Theory vfmTestDefs0983[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/call_ecrecover0_complete_return_value/call_ecrecover0_complete_return_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/call_ecrecover0_complete_return_value/call_ecrecover0_complete_return_value.json");
val defs = mapi (define_test "0983") tests;

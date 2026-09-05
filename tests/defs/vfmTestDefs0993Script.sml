Theory vfmTestDefs0993[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/call_ecrecover_check_length_wrong_v/call_ecrecover_check_length_wrong_v.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/call_ecrecover_check_length_wrong_v/call_ecrecover_check_length_wrong_v.json");
val defs = mapi (define_test "0993") tests;

Theory vfmTestDefs2513[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_ecrecover_check_length_wrong_v/static_call_ecrecover_check_length_wrong_v.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_ecrecover_check_length_wrong_v/static_call_ecrecover_check_length_wrong_v.json");
val defs = mapi (define_test "2513") tests;

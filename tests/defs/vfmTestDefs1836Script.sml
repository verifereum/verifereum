Theory vfmTestDefs1836[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_sha256_1_nonzero_value/static_call_sha256_1_nonzero_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_call_sha256_1_nonzero_value/static_call_sha256_1_nonzero_value.json");
val defs = mapi (define_test "1836") tests;

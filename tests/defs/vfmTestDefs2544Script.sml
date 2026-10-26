Theory vfmTestDefs2544[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_sha256_3/static_call_sha256_3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_sha256_3/static_call_sha256_3.json");
val defs = mapi (define_test "2544") tests;

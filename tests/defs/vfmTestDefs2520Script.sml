Theory vfmTestDefs2520[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_identity_4_gas18/static_call_identity_4_gas18.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_call_identity_4_gas18/static_call_identity_4_gas18.json");
val defs = mapi (define_test "2520") tests;

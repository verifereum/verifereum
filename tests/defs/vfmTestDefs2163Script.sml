Theory vfmTestDefs2163[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRipemd160_3_prefixed0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_CallRipemd160_3_prefixed0.json");
val defs = mapi (define_test "2163") tests;

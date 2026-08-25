Theory vfmTestDefs2162[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRipemd160_3_postfixed0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_CallRipemd160_3_postfixed0.json");
val defs = mapi (define_test "2162") tests;

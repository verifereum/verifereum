Theory vfmTestDefs2109[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000_ecrec.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_Call50000_ecrec.json");
val defs = mapi (define_test "2109") tests;

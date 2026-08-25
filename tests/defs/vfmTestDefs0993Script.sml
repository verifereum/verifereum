Theory vfmTestDefs0993[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stExample/indexesOmitExample.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stExample/indexesOmitExample.json");
val defs = mapi (define_test "0993") tests;

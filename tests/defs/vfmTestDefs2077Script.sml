Theory vfmTestDefs2077[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowM1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStackTests/stackOverflowM1.json");
val defs = mapi (define_test "2077") tests;

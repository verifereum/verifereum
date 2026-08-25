Theory vfmTestDefs2079[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowM1PUSH.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStackTests/stackOverflowM1PUSH.json");
val defs = mapi (define_test "2079") tests;

Theory vfmTestDefs2078[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowM1DUP.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStackTests/stackOverflowM1DUP.json");
val defs = mapi (define_test "2078") tests;

Theory vfmTestDefs1060[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stLogTests/log0_logMemsizeZero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stLogTests/log0_logMemsizeZero.json");
val defs = mapi (define_test "1060") tests;

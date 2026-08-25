Theory vfmTestDefs1059[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stLogTests/log0_logMemsizeTooHigh.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stLogTests/log0_logMemsizeTooHigh.json");
val defs = mapi (define_test "1059") tests;

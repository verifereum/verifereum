Theory vfmTestDefs1064[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stLogTests/log1_Caller.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stLogTests/log1_Caller.json");
val defs = mapi (define_test "1064") tests;

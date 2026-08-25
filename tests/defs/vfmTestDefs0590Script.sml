Theory vfmTestDefs0590[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcall_100_SuicideMiddle.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCodes/callcodecallcall_100_SuicideMiddle.json");
val defs = mapi (define_test "0590") tests;

Theory vfmTestDefs1957[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundEmptyCallOOG_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundEmptyCallOOG_Paris.json");
val defs = mapi (define_test "1957") tests;

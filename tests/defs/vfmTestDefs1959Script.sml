Theory vfmTestDefs1959[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundEmptyOOG_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRevertTest/RevertPrefoundEmptyOOG_Paris.json");
val defs = mapi (define_test "1959") tests;

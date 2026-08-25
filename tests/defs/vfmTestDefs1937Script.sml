Theory vfmTestDefs1937[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInStaticCall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRevertTest/RevertInStaticCall.json");
val defs = mapi (define_test "1937") tests;

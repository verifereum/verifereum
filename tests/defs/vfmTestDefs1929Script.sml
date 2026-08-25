Theory vfmTestDefs1929[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRevertTest/NashatyrevSuicideRevert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRevertTest/NashatyrevSuicideRevert.json");
val defs = mapi (define_test "1929") tests;

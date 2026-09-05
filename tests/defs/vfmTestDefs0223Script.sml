Theory vfmTestDefs0223[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/homestead/coverage/coverage/coverage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/homestead/coverage/coverage/coverage.json");
val defs = mapi (define_test "0223") tests;

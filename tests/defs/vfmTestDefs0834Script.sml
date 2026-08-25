Theory vfmTestDefs0834[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCreate2/returndatasize_following_successful_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCreate2/returndatasize_following_successful_create.json");
val defs = mapi (define_test "0834") tests;

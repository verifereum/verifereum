Theory vfmTestDefs1890[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_0_0_following_successful_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_0_0_following_successful_create.json");
val defs = mapi (define_test "1890") tests;

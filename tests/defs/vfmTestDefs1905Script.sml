Theory vfmTestDefs1905[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_following_too_big_transfer.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_following_too_big_transfer.json");
val defs = mapi (define_test "1905") tests;

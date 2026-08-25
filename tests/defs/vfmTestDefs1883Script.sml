Theory vfmTestDefs1883[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_ecrec_success_empty_then_returndatasize.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/call_ecrec_success_empty_then_returndatasize.json");
val defs = mapi (define_test "1883") tests;

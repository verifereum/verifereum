Theory vfmTestDefs1913[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_oog_after_deeper.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_oog_after_deeper.json");
val defs = mapi (define_test "1913") tests;

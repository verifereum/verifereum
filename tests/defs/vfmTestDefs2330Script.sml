Theory vfmTestDefs2330[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stReturnDataTest/returndatasize_after_oog_after_deeper/returndatasize_after_oog_after_deeper.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stReturnDataTest/returndatasize_after_oog_after_deeper/returndatasize_after_oog_after_deeper.json");
val defs = mapi (define_test "2330") tests;

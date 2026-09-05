Theory vfmTestDefs0591[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCodeSizeLimit/codesize_oog_invalid_size/codesize_oog_invalid_size.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCodeSizeLimit/codesize_oog_invalid_size/codesize_oog_invalid_size.json");
val defs = mapi (define_test "0591") tests;

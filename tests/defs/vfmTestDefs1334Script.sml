Theory vfmTestDefs1334[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCodeSizeLimit/codesize_init/codesize_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCodeSizeLimit/codesize_init/codesize_init.json");
val defs = mapi (define_test "1334") tests;

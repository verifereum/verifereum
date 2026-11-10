Theory vfmTestDefs1482[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP158Specific/extcodesize_to_epmty_paris/extcodesize_to_epmty_paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP158Specific/extcodesize_to_epmty_paris/extcodesize_to_epmty_paris.json");
val defs = mapi (define_test "1482") tests;

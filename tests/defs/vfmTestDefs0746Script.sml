Theory vfmTestDefs0746[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP158Specific/extcodesize_to_non_existent/extcodesize_to_non_existent.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP158Specific/extcodesize_to_non_existent/extcodesize_to_non_existent.json");
val defs = mapi (define_test "0746") tests;

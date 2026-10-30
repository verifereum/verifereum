Theory vfmTestDefs1313[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/callcode_with_high_value/callcode_with_high_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/callcode_with_high_value/callcode_with_high_value.json");
val defs = mapi (define_test "1313") tests;

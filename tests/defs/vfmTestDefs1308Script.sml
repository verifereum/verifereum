Theory vfmTestDefs1308[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/callcode_output2/callcode_output2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/callcode_output2/callcode_output2.json");
val defs = mapi (define_test "1308") tests;

Theory vfmTestDefs0440[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/call_output3partial/call_output3partial.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/call_output3partial/call_output3partial.json");
val defs = mapi (define_test "0440") tests;

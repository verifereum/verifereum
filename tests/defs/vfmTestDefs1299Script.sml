Theory vfmTestDefs1299[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/call_output3_fail/call_output3_fail.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCreateCallCodeTest/call_output3_fail/call_output3_fail.json");
val defs = mapi (define_test "1299") tests;

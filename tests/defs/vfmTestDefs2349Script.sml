Theory vfmTestDefs2349[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRevertTest/revert_in_call_code/revert_in_call_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRevertTest/revert_in_call_code/revert_in_call_code.json");
val defs = mapi (define_test "2349") tests;

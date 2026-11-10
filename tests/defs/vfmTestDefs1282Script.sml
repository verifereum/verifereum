Theory vfmTestDefs1282[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCodes/call_chain/two_level_call_chain.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCodes/call_chain/two_level_call_chain.json");
val defs = mapi (define_test "1282") tests;

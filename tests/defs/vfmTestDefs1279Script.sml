Theory vfmTestDefs1279[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCodes/call_chain/three_level_call_chain_suicide_end.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCodes/call_chain/three_level_call_chain_suicide_end.json");
val defs = mapi (define_test "1279") tests;

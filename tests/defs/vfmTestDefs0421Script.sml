Theory vfmTestDefs0421[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/call_chain/three_level_call_chain_oogm_after.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/call_chain/three_level_call_chain_oogm_after.json");
val defs = mapi (define_test "0421") tests;

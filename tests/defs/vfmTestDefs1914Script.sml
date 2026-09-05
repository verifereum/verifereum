Theory vfmTestDefs1914[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcallcodecallcode_011_oogm_before/static_callcallcodecallcode_011_oogm_before.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcallcodecallcode_011_oogm_before/static_callcallcodecallcode_011_oogm_before.json");
val defs = mapi (define_test "1914") tests;

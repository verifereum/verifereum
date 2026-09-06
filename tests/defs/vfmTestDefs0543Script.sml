Theory vfmTestDefs0543[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcallcodecall_010_oogm_before/callcallcodecall_010_oogm_before.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcallcodecall_010_oogm_before/callcallcodecall_010_oogm_before.json");
val defs = mapi (define_test "0543") tests;

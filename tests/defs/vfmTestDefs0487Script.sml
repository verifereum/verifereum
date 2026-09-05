Theory vfmTestDefs0487[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcallcodecall_010_suicide_middle/callcallcodecall_010_suicide_middle.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcallcodecall_010_suicide_middle/callcallcodecall_010_suicide_middle.json");
val defs = mapi (define_test "0487") tests;

Theory vfmTestDefs0552[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcallcodecallcode_011_suicide_middle/callcallcodecallcode_011_suicide_middle.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcallcodecallcode_011_suicide_middle/callcallcodecallcode_011_suicide_middle.json");
val defs = mapi (define_test "0552") tests;

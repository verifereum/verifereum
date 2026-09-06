Theory vfmTestDefs0547[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcallcodecallcode_011/callcallcodecallcode_011.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcallcodecallcode_011/callcallcodecallcode_011.json");
val defs = mapi (define_test "0547") tests;

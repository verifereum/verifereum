Theory vfmTestDefs0733[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_ABCB_RECURSIVE.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecall_ABCB_RECURSIVE.json");
val defs = mapi (define_test "0733") tests;

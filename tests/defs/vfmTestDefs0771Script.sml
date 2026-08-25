Theory vfmTestDefs0771[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecallcode_111_OOGMBefore.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcodecallcodecallcode_111_OOGMBefore.json");
val defs = mapi (define_test "0771") tests;

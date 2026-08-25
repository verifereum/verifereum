Theory vfmTestDefs0573[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecallcode_ABCB_RECURSIVE.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCodes/callcallcodecallcode_ABCB_RECURSIVE.json");
val defs = mapi (define_test "0573") tests;

Theory vfmTestDefs0611[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcodecallcode_111_OOGMAfter.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCodes/callcodecallcodecallcode_111_OOGMAfter.json");
val defs = mapi (define_test "0611") tests;

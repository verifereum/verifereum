Theory vfmTestDefs0541[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00_OOGE_valueTransfer.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCodes/callcall_00_OOGE_valueTransfer.json");
val defs = mapi (define_test "0541") tests;

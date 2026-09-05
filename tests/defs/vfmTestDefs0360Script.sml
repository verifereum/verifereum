Theory vfmTestDefs0360[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcall_00_ooge_value_transfer/callcall_00_ooge_value_transfer.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcall_00_ooge_value_transfer/callcall_00_ooge_value_transfer.json");
val defs = mapi (define_test "0360") tests;

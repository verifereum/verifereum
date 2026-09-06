Theory vfmTestDefs0363[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcallcall_000_ooge/callcallcall_000_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcallcall_000_ooge/callcallcall_000_ooge.json");
val defs = mapi (define_test "0363") tests;

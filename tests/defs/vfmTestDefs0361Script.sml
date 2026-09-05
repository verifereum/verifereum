Theory vfmTestDefs0361[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcall_00_suicide_end/callcall_00_suicide_end.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcall_00_suicide_end/callcall_00_suicide_end.json");
val defs = mapi (define_test "0361") tests;

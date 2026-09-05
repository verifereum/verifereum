Theory vfmTestDefs0520[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_suicide_end/callcodecallcodecall_110_suicide_end.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_suicide_end/callcodecallcodecall_110_suicide_end.json");
val defs = mapi (define_test "0520") tests;

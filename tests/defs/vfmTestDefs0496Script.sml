Theory vfmTestDefs0496[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecall_10/callcodecall_10.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecall_10/callcodecall_10.json");
val defs = mapi (define_test "0496") tests;

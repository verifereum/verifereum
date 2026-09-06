Theory vfmTestDefs0517[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_ooge/callcodecallcodecall_110_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_ooge/callcodecallcodecall_110_ooge.json");
val defs = mapi (define_test "0517") tests;

Theory vfmTestDefs0514[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcode_11_ooge/callcodecallcode_11_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcode_11_ooge/callcodecallcode_11_ooge.json");
val defs = mapi (define_test "0514") tests;

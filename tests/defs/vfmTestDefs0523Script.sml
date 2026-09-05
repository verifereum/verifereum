Theory vfmTestDefs0523[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcodecallcode_111/callcodecallcodecallcode_111.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesCallCodeHomestead/callcodecallcodecallcode_111/callcodecallcodecallcode_111.json");
val defs = mapi (define_test "0523") tests;

Theory vfmTestDefs0581[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcodecallcodecallcode_111/callcodecallcodecallcode_111.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcodecallcodecallcode_111/callcodecallcodecallcode_111.json");
val defs = mapi (define_test "0581") tests;

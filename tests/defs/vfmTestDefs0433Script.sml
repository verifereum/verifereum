Theory vfmTestDefs0433[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecallcodecallcode_abcb_recursive/callcodecallcodecallcode_abcb_recursive.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecallcodecallcode_abcb_recursive/callcodecallcodecallcode_abcb_recursive.json");
val defs = mapi (define_test "0433") tests;

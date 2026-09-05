Theory vfmTestDefs0420[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecallcodecall_110/callcodecallcodecall_110.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecallcodecall_110/callcodecallcodecall_110.json");
val defs = mapi (define_test "0420") tests;

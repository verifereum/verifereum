Theory vfmTestDefs0401[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecall_10_ooge/callcodecall_10_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecall_10_ooge/callcodecall_10_ooge.json");
val defs = mapi (define_test "0401") tests;

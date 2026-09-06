Theory vfmTestDefs0558[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcodecallcall_100_ooge/callcodecallcall_100_ooge.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallDelegateCodesHomestead/callcodecallcall_100_ooge/callcodecallcall_100_ooge.json");
val defs = mapi (define_test "0558") tests;

Theory vfmTestDefs2680[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcodecallcodecall_110_suicide_middle/static_callcodecallcodecall_110_suicide_middle.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcodecallcodecall_110_suicide_middle/static_callcodecallcodecall_110_suicide_middle.json");
val defs = mapi (define_test "2680") tests;

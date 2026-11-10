Theory vfmTestDefs2623[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcallcodecallcode_011_suicide_end2/static_callcallcodecallcode_011_suicide_end2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_callcallcodecallcode_011_suicide_end2/static_callcallcodecallcode_011_suicide_end2.json");
val defs = mapi (define_test "2623") tests;

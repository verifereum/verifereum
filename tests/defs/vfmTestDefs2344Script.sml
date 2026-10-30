Theory vfmTestDefs2344[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stRevertTest/nashatyrev_suicide_revert/nashatyrev_suicide_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stRevertTest/nashatyrev_suicide_revert/nashatyrev_suicide_revert.json");
val defs = mapi (define_test "2344") tests;

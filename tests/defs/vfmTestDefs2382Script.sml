Theory vfmTestDefs2382[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/StaticcallForPrecompilesIssue683.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticFlagEnabled/StaticcallForPrecompilesIssue683.json");
val defs = mapi (define_test "2382") tests;

Theory vfmTestDefs1872[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallToSuicideNoStorage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRefundTest/refund_CallToSuicideNoStorage.json");
val defs = mapi (define_test "1872") tests;

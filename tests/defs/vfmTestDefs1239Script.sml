Theory vfmTestDefs1239[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALL_ToNonNonZeroBalance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALL_ToNonNonZeroBalance.json");
val defs = mapi (define_test "1239") tests;

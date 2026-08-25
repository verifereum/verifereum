Theory vfmTestDefs2372[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithNOTZeroValueToPrecompileFromTransaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithNOTZeroValueToPrecompileFromTransaction.json");
val defs = mapi (define_test "2372") tests;

Theory vfmTestDefs0225[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_invalid.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7951_p256verify_precompiles/test_invalid.json");
val defs = mapi (define_test "0225") tests;

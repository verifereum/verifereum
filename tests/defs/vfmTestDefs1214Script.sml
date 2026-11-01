Theory vfmTestDefs1214[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/osaka/eip7951_p256verify_precompiles/p256verify/valid.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/osaka/eip7951_p256verify_precompiles/p256verify/valid.json");
val defs = mapi (define_test "1214") tests;

Theory vfmTestDefs0293[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7951_p256verify_precompiles/p256verify/modular_comparison.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7951_p256verify_precompiles/p256verify/modular_comparison.json");
val defs = mapi (define_test "0293") tests;

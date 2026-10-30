Theory vfmTestDefs1206[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/osaka/eip7951_p256verify_precompiles/p256verify/call_types.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/osaka/eip7951_p256verify_precompiles/p256verify/call_types.json");
val defs = mapi (define_test "1206") tests;

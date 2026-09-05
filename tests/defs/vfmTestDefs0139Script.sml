Theory vfmTestDefs0139[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/constantinople/eip1014_create2/create2_revert/create2_revert_preserves_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/constantinople/eip1014_create2/create2_revert/create2_revert_preserves_balance.json");
val defs = mapi (define_test "0139") tests;

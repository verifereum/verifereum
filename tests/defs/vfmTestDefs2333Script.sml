Theory vfmTestDefs2333[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip6110_deposits/modified_contract/invalid_log_length.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip6110_deposits/modified_contract/invalid_log_length.json");
val defs = mapi (define_test "2333") tests;

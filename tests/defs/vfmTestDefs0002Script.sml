Theory vfmTestDefs0002[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_first_write_of_authority.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/authorization_charges/account_write_first_write_of_authority.json");
val defs = mapi (define_test "0002") tests;

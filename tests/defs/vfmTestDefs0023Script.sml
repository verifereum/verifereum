Theory vfmTestDefs0023[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/calldata_floor/calldata_floor_with_authorizations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/calldata_floor/calldata_floor_with_authorizations.json");
val defs = mapi (define_test "0023") tests;

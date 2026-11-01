Theory vfmTestDefs0027[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/intrinsic_gas_boundary/intrinsic_gas_floor_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip2780_reduce_intrinsic_tx_gas/intrinsic_gas_boundary/intrinsic_gas_floor_boundary.json");
val defs = mapi (define_test "0027") tests;

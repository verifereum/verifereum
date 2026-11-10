Theory vfmTestDefs0105[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7778_block_gas_accounting_without_refunds/gas_accounting/trailing_tx_admission_uses_pre_refund_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7778_block_gas_accounting_without_refunds/gas_accounting/trailing_tx_admission_uses_pre_refund_gas.json");
val defs = mapi (define_test "0105") tests;

Theory vfmTestDefs0108[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7778_block_gas_accounting_without_refunds/transaction_types/block_gas_accounting_with_logs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7778_block_gas_accounting_without_refunds/transaction_types/block_gas_accounting_with_logs.json");
val defs = mapi (define_test "0108") tests;

Theory vfmTestDefs0104[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7778_block_gas_accounting_without_refunds/gas_accounting/simple_gas_accounting.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7778_block_gas_accounting_without_refunds/gas_accounting/simple_gas_accounting.json");
val defs = mapi (define_test "0104") tests;

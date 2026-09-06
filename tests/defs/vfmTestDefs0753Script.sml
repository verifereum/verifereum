Theory vfmTestDefs0753[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP2930/transaction_costs/transaction_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP2930/transaction_costs/transaction_costs.json");
val defs = mapi (define_test "0753") tests;

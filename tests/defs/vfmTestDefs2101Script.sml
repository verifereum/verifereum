Theory vfmTestDefs2101[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/high_gas_limit/high_gas_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/high_gas_limit/high_gas_limit.json");
val defs = mapi (define_test "2101") tests;

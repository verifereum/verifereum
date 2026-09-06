Theory vfmTestDefs0732[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1559/low_gas_limit/low_gas_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1559/low_gas_limit/low_gas_limit.json");
val defs = mapi (define_test "0732") tests;

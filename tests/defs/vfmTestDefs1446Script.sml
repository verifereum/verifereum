Theory vfmTestDefs1446[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP150Specific/new_gas_price_for_codes/new_gas_price_for_codes.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP150Specific/new_gas_price_for_codes/new_gas_price_for_codes.json");
val defs = mapi (define_test "1446") tests;

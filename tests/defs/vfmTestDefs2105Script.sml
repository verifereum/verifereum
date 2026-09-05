Theory vfmTestDefs2105[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/internal_call_hitting_gas_limit_success/internal_call_hitting_gas_limit_success.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/internal_call_hitting_gas_limit_success/internal_call_hitting_gas_limit_success.json");
val defs = mapi (define_test "2105") tests;

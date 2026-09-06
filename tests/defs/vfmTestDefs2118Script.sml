Theory vfmTestDefs2118[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/suicides_and_internal_call_suicides_bonus_gas_at_call_failed/suicides_and_internal_call_suicides_bonus_gas_at_call_failed.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/suicides_and_internal_call_suicides_bonus_gas_at_call_failed/suicides_and_internal_call_suicides_bonus_gas_at_call_failed.json");
val defs = mapi (define_test "2118") tests;

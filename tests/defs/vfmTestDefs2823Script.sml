Theory vfmTestDefs2823[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stTransactionTest/suicides_and_internal_call_suicides_bonus_gas_at_call/suicides_and_internal_call_suicides_bonus_gas_at_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stTransactionTest/suicides_and_internal_call_suicides_bonus_gas_at_call/suicides_and_internal_call_suicides_bonus_gas_at_call.json");
val defs = mapi (define_test "2823") tests;

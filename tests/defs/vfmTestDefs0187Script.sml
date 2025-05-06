open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0187";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/system_contract_errors.json";
val defs = mapi (define_test "0187") tests;
val () = export_theory_no_docs ();

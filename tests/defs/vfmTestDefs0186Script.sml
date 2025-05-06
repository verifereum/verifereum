open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0186";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/extra_withdrawals.json";
val defs = mapi (define_test "0186") tests;
val () = export_theory_no_docs ();

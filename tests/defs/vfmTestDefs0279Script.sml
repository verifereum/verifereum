open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0279";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_withdrawal_requests_during_fork.json";
val defs = mapi (define_test "0279") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0190";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/withdrawal_requests_during_fork/withdrawal_requests_during_fork.json";
val defs = mapi (define_test "0190") tests;
val () = export_theory_no_docs ();

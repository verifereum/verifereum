open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0188";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/withdrawal_requests/withdrawal_requests.json";
val defs = mapi (define_test "0188") tests;
val () = export_theory_no_docs ();

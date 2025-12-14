open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0274";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_eip_7002.json";
val defs = mapi (define_test "0274") tests;
val () = export_theory_no_docs ();

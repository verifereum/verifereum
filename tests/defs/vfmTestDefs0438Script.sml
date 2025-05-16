open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0438";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stAttackTest/ContractCreationSpam.json";
val defs = mapi (define_test "0438") tests;
val () = export_theory_no_docs ();

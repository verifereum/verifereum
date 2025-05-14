open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0686";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createNameRegistratorPreStore1NotEnoughGas.json";
val defs = mapi (define_test "0686") tests;
val () = export_theory_no_docs ();

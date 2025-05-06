open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1350";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallIdentitiy_1.json";
val defs = mapi (define_test "1350") tests;
val () = export_theory_no_docs ();

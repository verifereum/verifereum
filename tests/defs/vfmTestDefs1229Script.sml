open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1229";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverInvalidSignature.json";
val defs = mapi (define_test "1229") tests;
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1260";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallSha256_3_prefix0.json";
val defs = mapi (define_test "1260") tests;
val () = export_theory_no_docs ();

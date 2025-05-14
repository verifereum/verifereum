open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2454";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithZeroValueToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2454") tests;
val () = export_theory_no_docs ();

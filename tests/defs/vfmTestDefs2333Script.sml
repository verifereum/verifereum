open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2333";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/CallWithNOTZeroValueToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2333") tests;
val () = export_theory_no_docs ();

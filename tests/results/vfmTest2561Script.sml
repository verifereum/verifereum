open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2561Theory;
val () = new_theory "vfmTest2561";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2561") $ get_result_defs "vfmTestDefs2561";
val () = export_theory_no_docs ();

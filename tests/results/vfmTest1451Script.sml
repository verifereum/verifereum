open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1451Theory;
val () = new_theory "vfmTest1451";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1451") $ get_result_defs "vfmTestDefs1451";
val () = export_theory_no_docs ();

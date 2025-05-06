open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1989Theory;
val () = new_theory "vfmTest1989";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1989") $ get_result_defs "vfmTestDefs1989";
val () = export_theory_no_docs ();

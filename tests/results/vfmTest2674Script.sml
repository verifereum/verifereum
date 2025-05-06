open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2674Theory;
val () = new_theory "vfmTest2674";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2674") $ get_result_defs "vfmTestDefs2674";
val () = export_theory_no_docs ();

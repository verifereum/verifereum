open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1746Theory;
val () = new_theory "vfmTest1746";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1746") $ get_result_defs "vfmTestDefs1746";
val () = export_theory_no_docs ();

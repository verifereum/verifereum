open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1463Theory;
val () = new_theory "vfmTest1463";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1463") $ get_result_defs "vfmTestDefs1463";
val () = export_theory_no_docs ();

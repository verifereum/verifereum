open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1127Theory;
val () = new_theory "vfmTest1127";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1127") $ get_result_defs "vfmTestDefs1127";
val () = export_theory_no_docs ();

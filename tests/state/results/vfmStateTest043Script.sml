open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs043Theory;
val () = new_theory "vfmStateTest043";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs043") $ get_result_defs "vfmStateTestDefs043";
val () = export_theory_no_docs ();

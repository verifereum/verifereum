open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs070Theory;
val () = new_theory "vfmStateTest070";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs070") $ get_result_defs "vfmStateTestDefs070";
val () = export_theory_no_docs ();

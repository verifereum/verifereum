open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs201Theory;
val () = new_theory "vfmStateTest201";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs201") $ get_result_defs "vfmStateTestDefs201";
val () = export_theory_no_docs ();

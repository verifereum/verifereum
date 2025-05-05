open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs113Theory;
val () = new_theory "vfmStateTest113";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs113") $ get_result_defs "vfmStateTestDefs113";
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs090Theory;
val () = new_theory "vfmStateTest090";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs090";
val () = export_theory_no_docs ();

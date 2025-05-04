open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs182Theory;
val () = new_theory "vfmStateTest182";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs182";
val () = export_theory_no_docs ();

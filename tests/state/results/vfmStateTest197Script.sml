open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs197Theory;
val () = new_theory "vfmStateTest197";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs197";
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs107Theory;
val () = new_theory "vfmStateTest107";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs107";
val () = export_theory_no_docs ();

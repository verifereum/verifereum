open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs130Theory;
val () = new_theory "vfmStateTest130";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs130";
val () = export_theory_no_docs ();

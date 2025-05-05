open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs027Theory;
val () = new_theory "vfmStateTest027";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs027") $ get_result_defs "vfmStateTestDefs027";
val () = export_theory_no_docs ();

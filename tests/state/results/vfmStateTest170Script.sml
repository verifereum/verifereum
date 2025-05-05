open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs170Theory;
val () = new_theory "vfmStateTest170";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs170") $ get_result_defs "vfmStateTestDefs170";
val () = export_theory_no_docs ();

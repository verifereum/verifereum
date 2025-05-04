open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs176Theory;
val () = new_theory "vfmStateTest176";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs176";
val () = export_theory_no_docs ();

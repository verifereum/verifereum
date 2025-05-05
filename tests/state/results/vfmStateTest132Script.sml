open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs132Theory;
val () = new_theory "vfmStateTest132";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs132") $ get_result_defs "vfmStateTestDefs132";
val () = export_theory_no_docs ();

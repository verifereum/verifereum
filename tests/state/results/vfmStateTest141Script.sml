open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs141Theory;
val () = new_theory "vfmStateTest141";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs141") $ get_result_defs "vfmStateTestDefs141";
val () = export_theory_no_docs ();

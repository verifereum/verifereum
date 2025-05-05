open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs171Theory;
val () = new_theory "vfmStateTest171";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs171") $ get_result_defs "vfmStateTestDefs171";
val () = export_theory_no_docs ();

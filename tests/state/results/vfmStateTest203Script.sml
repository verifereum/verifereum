open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs203Theory;
val () = new_theory "vfmStateTest203";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs203") $ get_result_defs "vfmStateTestDefs203";
val () = export_theory_no_docs ();

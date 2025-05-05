open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs174Theory;
val () = new_theory "vfmStateTest174";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs174") $ get_result_defs "vfmStateTestDefs174";
val () = export_theory_no_docs ();

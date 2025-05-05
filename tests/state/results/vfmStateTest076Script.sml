open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs076Theory;
val () = new_theory "vfmStateTest076";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs076") $ get_result_defs "vfmStateTestDefs076";
val () = export_theory_no_docs ();

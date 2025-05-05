open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs099Theory;
val () = new_theory "vfmStateTest099";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs099") $ get_result_defs "vfmStateTestDefs099";
val () = export_theory_no_docs ();

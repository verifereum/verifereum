open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs085Theory;
val () = new_theory "vfmStateTest085";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs085") $ get_result_defs "vfmStateTestDefs085";
val () = export_theory_no_docs ();

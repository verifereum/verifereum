open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs063Theory;
val () = new_theory "vfmStateTest063";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs063";
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs101Theory;
val () = new_theory "vfmStateTest101";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs101") $ get_result_defs "vfmStateTestDefs101";
val () = export_theory_no_docs ();

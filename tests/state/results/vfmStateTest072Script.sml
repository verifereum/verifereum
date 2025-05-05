open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs072Theory;
val () = new_theory "vfmStateTest072";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs072") $ get_result_defs "vfmStateTestDefs072";
val () = export_theory_no_docs ();

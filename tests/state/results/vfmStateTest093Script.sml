open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs093Theory;
val () = new_theory "vfmStateTest093";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs093";
val () = export_theory_no_docs ();

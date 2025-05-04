open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs127Theory;
val () = new_theory "vfmStateTest127";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs127";
val () = export_theory_no_docs ();

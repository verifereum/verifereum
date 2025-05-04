open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs129Theory;
val () = new_theory "vfmStateTest129";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs129";
val () = export_theory_no_docs ();

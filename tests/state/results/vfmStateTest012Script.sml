open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs012Theory;
val () = new_theory "vfmStateTest012";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs012") $ get_result_defs "vfmStateTestDefs012";
val () = export_theory_no_docs ();

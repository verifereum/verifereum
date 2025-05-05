open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs206Theory;
val () = new_theory "vfmStateTest206";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs206") $ get_result_defs "vfmStateTestDefs206";
val () = export_theory_no_docs ();

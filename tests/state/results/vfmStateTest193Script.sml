open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs193Theory;
val () = new_theory "vfmStateTest193";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs193") $ get_result_defs "vfmStateTestDefs193";
val () = export_theory_no_docs ();

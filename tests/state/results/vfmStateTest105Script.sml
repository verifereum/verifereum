open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs105Theory;
val () = new_theory "vfmStateTest105";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs105";
val () = export_theory_no_docs ();

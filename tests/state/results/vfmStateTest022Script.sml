open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs022Theory;
val () = new_theory "vfmStateTest022";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs022") $ get_result_defs "vfmStateTestDefs022";
val () = export_theory_no_docs ();

open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs031Theory;
val () = new_theory "vfmStateTest031";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs031") $ get_result_defs "vfmStateTestDefs031";
val () = export_theory_no_docs ();

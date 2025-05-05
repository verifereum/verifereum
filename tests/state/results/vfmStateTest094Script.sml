open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs094Theory;
val () = new_theory "vfmStateTest094";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs094") $ get_result_defs "vfmStateTestDefs094";
val () = export_theory_no_docs ();

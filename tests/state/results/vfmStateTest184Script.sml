open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs184Theory;
val () = new_theory "vfmStateTest184";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs184") $ get_result_defs "vfmStateTestDefs184";
val () = export_theory_no_docs ();

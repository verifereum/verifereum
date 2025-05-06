open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1236Theory;
val () = new_theory "vfmTest1236";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1236") $ get_result_defs "vfmTestDefs1236";
val () = export_theory_no_docs ();

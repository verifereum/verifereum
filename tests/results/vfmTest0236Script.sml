open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0236Theory;
val () = new_theory "vfmTest0236";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0236") $ get_result_defs "vfmTestDefs0236";
val () = export_theory_no_docs ();

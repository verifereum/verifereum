open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs028Theory;
val () = new_theory "vfmStateTest028";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs028") $ get_result_defs "vfmStateTestDefs028";
val () = export_theory_no_docs ();

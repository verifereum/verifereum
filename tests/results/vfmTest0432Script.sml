open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0432Theory;
val () = new_theory "vfmTest0432";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0432") $ get_result_defs "vfmTestDefs0432";
val () = export_theory_no_docs ();

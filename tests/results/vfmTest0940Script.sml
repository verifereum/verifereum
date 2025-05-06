open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0940Theory;
val () = new_theory "vfmTest0940";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0940") $ get_result_defs "vfmTestDefs0940";
val () = export_theory_no_docs ();

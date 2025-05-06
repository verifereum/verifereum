open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0667Theory;
val () = new_theory "vfmTest0667";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0667") $ get_result_defs "vfmTestDefs0667";
val () = export_theory_no_docs ();

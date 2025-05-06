open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0667Theory;
val () = new_theory "vfmTest0667";
val thyn = "vfmTestDefs0667";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();

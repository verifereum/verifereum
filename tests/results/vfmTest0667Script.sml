Theory vfmTest0667[no_sig_docs]
Ancestors vfmTestDefs0667
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0667_0.nsv", "result0667_1.nsv", "result0667_2.nsv", "result0667_3.nsv", "result0667_4.nsv", "result0667_5.nsv", "result0667_6.nsv", "result0667_7.nsv", "result0667_8.nsv", "result0667_9.nsv", "result0667_10.nsv", "result0667_11.nsv", "result0667_12.nsv", "result0667_13.nsv", "result0667_14.nsv", "result0667_15.nsv", "result0667_16.nsv", "result0667_17.nsv", "result0667_18.nsv", "result0667_19.nsv", "result0667_20.nsv", "result0667_21.nsv", "result0667_22.nsv", "result0667_23.nsv"];
val thyn = "vfmTestDefs0667";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0775[no_sig_docs]
Ancestors vfmTestDefs0775
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0775_0.nsv", "result0775_1.nsv", "result0775_2.nsv", "result0775_3.nsv", "result0775_4.nsv", "result0775_5.nsv", "result0775_6.nsv", "result0775_7.nsv", "result0775_8.nsv", "result0775_9.nsv", "result0775_10.nsv", "result0775_11.nsv", "result0775_12.nsv", "result0775_13.nsv", "result0775_14.nsv", "result0775_15.nsv", "result0775_16.nsv", "result0775_17.nsv", "result0775_18.nsv", "result0775_19.nsv", "result0775_20.nsv", "result0775_21.nsv"];
val thyn = "vfmTestDefs0775";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

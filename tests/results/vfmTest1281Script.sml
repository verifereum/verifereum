Theory vfmTest1281[no_sig_docs]
Ancestors vfmTestDefs1281
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1281_0.nsv", "result1281_1.nsv", "result1281_2.nsv", "result1281_3.nsv", "result1281_4.nsv", "result1281_5.nsv", "result1281_6.nsv", "result1281_7.nsv", "result1281_8.nsv", "result1281_9.nsv", "result1281_10.nsv", "result1281_11.nsv", "result1281_12.nsv", "result1281_13.nsv", "result1281_14.nsv", "result1281_15.nsv", "result1281_16.nsv", "result1281_17.nsv", "result1281_18.nsv", "result1281_19.nsv", "result1281_20.nsv", "result1281_21.nsv", "result1281_22.nsv", "result1281_23.nsv", "result1281_24.nsv", "result1281_25.nsv", "result1281_26.nsv"];
val thyn = "vfmTestDefs1281";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

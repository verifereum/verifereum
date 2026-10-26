Theory vfmTest3038[no_sig_docs]
Ancestors vfmTestDefs3038
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3038_0.nsv", "result3038_1.nsv", "result3038_2.nsv", "result3038_3.nsv", "result3038_4.nsv", "result3038_5.nsv", "result3038_6.nsv", "result3038_7.nsv", "result3038_8.nsv", "result3038_9.nsv", "result3038_10.nsv", "result3038_11.nsv", "result3038_12.nsv", "result3038_13.nsv", "result3038_14.nsv", "result3038_15.nsv", "result3038_16.nsv", "result3038_17.nsv", "result3038_18.nsv", "result3038_19.nsv"];
val thyn = "vfmTestDefs3038";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest3155[no_sig_docs]
Ancestors vfmTestDefs3155
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3155_0.nsv", "result3155_1.nsv", "result3155_2.nsv", "result3155_3.nsv", "result3155_4.nsv", "result3155_5.nsv", "result3155_6.nsv", "result3155_7.nsv", "result3155_8.nsv", "result3155_9.nsv", "result3155_10.nsv", "result3155_11.nsv", "result3155_12.nsv", "result3155_13.nsv", "result3155_14.nsv", "result3155_15.nsv", "result3155_16.nsv", "result3155_17.nsv", "result3155_18.nsv", "result3155_19.nsv"];
val thyn = "vfmTestDefs3155";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

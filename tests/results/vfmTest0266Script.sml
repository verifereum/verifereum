Theory vfmTest0266[no_sig_docs]
Ancestors vfmTestDefs0266
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0266_0.nsv", "result0266_1.nsv", "result0266_2.nsv", "result0266_3.nsv", "result0266_4.nsv", "result0266_5.nsv", "result0266_6.nsv", "result0266_7.nsv", "result0266_8.nsv", "result0266_9.nsv", "result0266_10.nsv", "result0266_11.nsv", "result0266_12.nsv", "result0266_13.nsv", "result0266_14.nsv", "result0266_15.nsv", "result0266_16.nsv", "result0266_17.nsv", "result0266_18.nsv", "result0266_19.nsv", "result0266_20.nsv", "result0266_21.nsv", "result0266_22.nsv", "result0266_23.nsv", "result0266_24.nsv", "result0266_25.nsv", "result0266_26.nsv", "result0266_27.nsv", "result0266_28.nsv", "result0266_29.nsv"];
val thyn = "vfmTestDefs0266";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

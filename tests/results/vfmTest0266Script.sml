Theory vfmTest0266[no_sig_docs]
Ancestors vfmTestDefs0266
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0266_0.nsv", "result0266_1.nsv", "result0266_2.nsv", "result0266_3.nsv", "result0266_4.nsv", "result0266_5.nsv", "result0266_6.nsv", "result0266_7.nsv", "result0266_8.nsv", "result0266_9.nsv", "result0266_10.nsv", "result0266_11.nsv", "result0266_12.nsv", "result0266_13.nsv"];
val thyn = "vfmTestDefs0266";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0602[no_sig_docs]
Ancestors vfmTestDefs0602
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0602_0.nsv", "result0602_1.nsv", "result0602_2.nsv", "result0602_3.nsv", "result0602_4.nsv", "result0602_5.nsv", "result0602_6.nsv", "result0602_7.nsv", "result0602_8.nsv", "result0602_9.nsv", "result0602_10.nsv", "result0602_11.nsv", "result0602_12.nsv", "result0602_13.nsv", "result0602_14.nsv", "result0602_15.nsv", "result0602_16.nsv", "result0602_17.nsv", "result0602_18.nsv", "result0602_19.nsv", "result0602_20.nsv", "result0602_21.nsv", "result0602_22.nsv", "result0602_23.nsv"];
val thyn = "vfmTestDefs0602";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

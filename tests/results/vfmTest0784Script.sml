Theory vfmTest0784[no_sig_docs]
Ancestors vfmTestDefs0784
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0784_0.nsv", "result0784_1.nsv", "result0784_2.nsv", "result0784_3.nsv", "result0784_4.nsv", "result0784_5.nsv", "result0784_6.nsv", "result0784_7.nsv", "result0784_8.nsv", "result0784_9.nsv", "result0784_10.nsv", "result0784_11.nsv", "result0784_12.nsv", "result0784_13.nsv", "result0784_14.nsv", "result0784_15.nsv", "result0784_16.nsv", "result0784_17.nsv", "result0784_18.nsv", "result0784_19.nsv", "result0784_20.nsv", "result0784_21.nsv", "result0784_22.nsv", "result0784_23.nsv"];
val thyn = "vfmTestDefs0784";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
